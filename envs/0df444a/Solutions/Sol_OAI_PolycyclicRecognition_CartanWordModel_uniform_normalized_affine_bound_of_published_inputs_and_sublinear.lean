-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:57:46.513135+00:00
-- url     : https://prove2.me/submissions/bea4ef63-15d7-424c-82d4-7baa5b69cea3

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D021
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_ray_boundary_family_homeomorphisms
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_nonempty_rayBoundaryComparison_of_shadows_m
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_boundary_comparisons

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FactorQuotientAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient action descends through overlapping group factors

The factors need not form a direct or injective semidirect decomposition.
The only overlap condition is that the nilpotent quotient kills it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N D Q G : Type} [Group N] [Group D] [Group Q] [Group G]

/-- Killing the overlap makes the affine action well-defined on the ambient
group, even when multiplication of the two factors is not injective. -/
theorem exists_descended_factor_quotient_action
    (ι : N →* G) (κ : D →* G) (hι : Function.Injective ι)
    (a : D →* MulAut N)
    (hconj : ∀ d n, ι (a d n) = κ d * ι n * (κ d)⁻¹)
    (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (π : N →* Q) (s : Q → N) (hs : Function.RightInverse s π)
    (ha : ∀ d n, a d n ∈ π.ker ↔ n ∈ π.ker)
    (hoverlap : ∀ n d, ι n = κ d → π n = 1) :
    ∃ act : G →* Equiv.Perm Q,
      (∀ n d q, act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ ι n * κ d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have hcompat (d) : ι.comp (a d).toMonoidHom = (MulAut.conj (κ d)).toMonoidHom.comp ι := by
    ext n
    exact hconj d n
  let σ : (N ⋊[a] D) →* G := SemidirectProduct.lift ι κ hcompat
  have hσ : Function.Surjective σ := by
    intro g
    obtain ⟨⟨n, d⟩, h⟩ := hsurj g
    exact ⟨⟨n, d⟩, h⟩
  let ρ := factorQuotientAction π s hs a ha
  have hker : σ.ker ≤ ρ.ker := by
    intro p hp
    have hp' : ι p.left * κ p.right = 1 := hp
    have hn : ι p.left = κ (p.right⁻¹) := by
      simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul, map_inv] using
        congrArg (fun x => x * (κ p.right)⁻¹) hp'
    have hπn : π p.left = 1 := hoverlap _ _ hn
    have hk : κ p.right = ι (p.left⁻¹) := by
      simpa only [map_inv, inv_mul_cancel_left, mul_one] using
        congrArg (fun x => (ι p.left)⁻¹ * x) hp'
    have had (x : N) : a p.right x = p.left⁻¹ * x * p.left := by
      apply hι
      rw [hconj, hk]
      simp only [map_mul, map_inv, inv_inv]
    apply Equiv.ext
    intro q
    obtain ⟨x, rfl⟩ := hs.surjective q
    change π p.left * descendQuotientAction π s hs a ha p.right (π x) = π x
    rw [descendQuotientAction_project, had]
    simp only [map_mul, map_inv, hπn, inv_one, one_mul, mul_one]
  let act := σ.liftOfSurjective hσ ⟨ρ, hker⟩
  have hact (p : N ⋊[a] D) : act (σ p) = ρ p :=
    σ.liftOfRightInverse_comp_apply _ _ _ p
  have hformula (n : N) (d : D) (q : Q) :
      act (ι n * κ d) q = π n * descendQuotientAction π s hs a ha d q := by
    exact congrArg (fun f : Equiv.Perm Q => f q) (hact ⟨n, d⟩)
  refine ⟨act, hformula, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨⟨n, d⟩, he⟩ := hsurj g
      refine ⟨n, d, ?_, he⟩
      rw [← he, hformula, map_one, mul_one] at hg
      exact hg
    · rintro ⟨n, d, hn, rfl⟩
      rw [hformula, map_one, mul_one]
      exact hn
  · intro g h
    exact congrArg (fun f : Equiv.Perm Q => f 1) (act.map_mul g h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCharts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The two product charts of the space of quasi-inverse pairs

Target normalization gives `G × X`; inverse normalization gives `X × G`,
where the latter copy of `X` represents inverse maps. Their transition is
an actual homeomorphism. This is the geometric coordinate change used for
the inverse-coupling measure, before any disintegration or fiber averaging.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

theorem pairChartTransition_forward (z : G) (p : NormalizedPair G Λ) (t : G) :
    (pairChartTransition (z, p)).1.val.1 t =
      (p.val.2 z⁻¹)⁻¹ * p.val.2 (z⁻¹ * t) := by
  change (p.val.2 (z⁻¹ * 1))⁻¹ * p.val.2 (z⁻¹ * (1 * t)) = _
  simp only [mul_one, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SublinearRayIdentification
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying bounded trace errors along linearly growing height rays -/

noncomputable section
namespace PolycyclicRecognition

/-- A metric sublinear error restricts to a sublinear error on every ray of
at most linear metric growth. The additive constant may depend on the ray. -/
theorem sublinear_error_on_linear_ray
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (base : X) (error : X → W) (ray : ℝ → X)
    (herror : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ x,
      ‖error x‖ ≤ ε * dist base x + B)
    {L C : ℝ} (hL : 0 ≤ L)
    (hmetric : ∀ t : ℝ, 0 ≤ t → dist base (ray t) ≤ L * t + C) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ t : ℝ, R ≤ t → 0 ≤ t →
      ‖error (ray t)‖ ≤ ε * t := by
  intro ε hε
  let δ := ε / (2 * (L + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (2 * (L + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hδL : δ * L ≤ ε / 2 := by nlinarith
  obtain ⟨B, hB⟩ := herror δ hδ
  refine ⟨2 * (δ * C + B) / ε, ?_⟩
  intro t ht ht0
  have hconst : 2 * (δ * C + B) ≤ t * ε := (div_le_iff₀ hε).mp ht
  have hslope := mul_le_mul_of_nonneg_right hδL ht0
  calc
    ‖error (ray t)‖ ≤ δ * dist base (ray t) + B := hB _
    _ ≤ δ * (L * t + C) + B := add_le_add (mul_le_mul_of_nonneg_left (hmetric t ht0) hδ.le) le_rfl
    _ ≤ ε * t := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialCoarseMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse metric bounds for exponential lines -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- Continuity on one fixed unit ball and the one-parameter identity give
one uniform coarse metric bound for all exponential directions. -/
theorem continuous_radial_exponential_metric_bound
    (Exp : V → G) (hcont : Continuous Exp) (hzero : Exp 0 = 1)
    (hmul : ∀ v : V, ∀ s t : ℝ, Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V, dist 1 (Exp v) ≤ C * (1 + ‖v‖) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V) 1).exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : V => (1 : G))).dist hcont).continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro v
  let n := ⌊‖v‖⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊‖v‖⌋₊)
  have hvn : ‖v‖ ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one ‖v‖).le
  have hnv : (n : ℝ) ≤ ‖v‖ + 1 := by
    have hh := Nat.floor_le (norm_nonneg v)
    dsimp [n]
    push_cast
    linarith
  let w := (n : ℝ)⁻¹ • v
  have hw : w ∈ closedBall (0 : V) 1 := by
    rw [mem_closedBall, dist_zero_right]
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact (inv_mul_le_iff₀ hn).mpr (by simpa using hvn)
  have hlocal : dist 1 (Exp w) ≤ B := by
    have hh := (hC w hw).trans (le_max_left C 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hh
  have hpow : ∀ k : ℕ, Exp ((k : ℝ) • w) = Exp w ^ k := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih => rw [Nat.cast_succ, hmul, ih, one_smul, pow_succ]
  have hv : (n : ℝ) • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
  conv_lhs => rw [← hv, hpow n]
  apply (dist_one_pow_le _ _).trans
  calc
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left hlocal hn.le
    _ ≤ B * (1 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHeightRays
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan representatives of height rays

The height is exactly linear along these rays. Continuity on one compact
ball and the one-parameter group identity give their linear metric growth.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

namespace CartanFactorModel

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [Group G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG) (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] in
/-- These are actual ambient height rays, with no coordinate approximation. -/
theorem heightRay_height (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (w : W) (t : ℝ) :
    (height (F.inclusionD (F.heightRay T eW w t))).toAdd = t • w := by
  rw [heightRay, F.compatibleD, hheight]
  change eW (heightProjection T.character
    (t • (cartanHeightSection T H (eW.symm w) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = t • w
  rw [map_smul, cartanHeightSection_height, map_smul, eW.apply_symm_apply]

set_option maxHeartbeats 1000000 in
/-- One metric coefficient works for all directions. The cost of direction
`w` is its norm in the chosen finite-dimensional height space. -/
theorem exists_heightRay_metric_bound [IsIsometricSMul G G]
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : W) (t : ℝ),
      dist 1 (F.inclusionD (F.heightRay T eW w t)) ≤ C * (1 + |t| * ‖w‖) := by
  let s := F.D.equiv.toLinearEquiv.toLinearMap.comp
    ((cartanHeightSection T H).comp eW.symm.toLinearMap)
  let E : W → G := fun w => F.inclusionD (F.ExpD (s w))
  have hE : Continuous E := by
    have he : E = F.inclusionD ∘ chartD ∘ s := by
      funext w
      exact congrArg F.inclusionD (hchartD (s w)).symm
    rw [he]
    exact F.closedD.continuous.comp (chartD.continuous.comp s.continuous_of_finiteDimensional)
  have hE0 : E 0 = 1 := by simp only [E, map_zero, F.isExpD.map_zero, map_one]
  have hadd (w : W) (x y : ℝ) : E ((x + y) • w) = E (x • w) * E (y • w) := by
    simp only [E, map_smul, F.isExpD.map_add_smul, map_mul]
  obtain ⟨C, hC, hbound⟩ := continuous_radial_exponential_metric_bound E hE hE0 hadd
  refine ⟨C, hC, ?_⟩
  intro w t
  have hb := hbound (t • w)
  simpa only [E, s, LinearMap.comp_apply, map_smul, heightRay, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, norm_smul, Real.norm_eq_abs] using hb


end CartanFactorModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SublinearHeightComposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing the linear coefficients of sublinear height maps -/

noncomputable section
namespace PolycyclicRecognition

/-- Uniform two-point sublinear errors compose. The coarse additive metric
constant contributes only to the new additive height constant. -/
theorem two_point_sublinear_height_comp
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (height : X → W) (f g : X → X) (A B : W →L[ℝ] W)
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hfLip : ∀ x y, dist (f x) (f y) ≤ L * dist x y + C)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (f y) - height (f x) - A (height y - height x)‖ ≤ ε * dist x y + D)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (g y) - height (g x) - B (height y - height x)‖ ≤ ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (g (f y)) - height (g (f x)) - (B.comp A) (height y - height x)‖ ≤
        ε * dist x y + D := by
  intro ε hε
  let δ := ε / (2 * (L + ‖B‖ + 1))
  have hden : 0 < 2 * (L + ‖B‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (2 * (L + ‖B‖ + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨Df, hDf, hfb⟩ := hf δ hδ
  obtain ⟨Dg, hDg, hgb⟩ := hg δ hδ
  refine ⟨δ * C + Dg + ‖B‖ * Df, by positivity, ?_⟩
  intro x y
  have he : height (g (f y)) - height (g (f x)) - (B.comp A) (height y - height x) =
      (height (g (f y)) - height (g (f x)) - B (height (f y) - height (f x))) +
        B (height (f y) - height (f x) - A (height y - height x)) := by
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    abel
  have hslope : δ * (L + ‖B‖) ≤ ε := by nlinarith [norm_nonneg B]
  rw [he]
  calc
    _ ≤ ‖height (g (f y)) - height (g (f x)) - B (height (f y) - height (f x))‖ +
        ‖B (height (f y) - height (f x) - A (height y - height x))‖ := norm_add_le _ _
    _ ≤ (δ * dist (f x) (f y) + Dg) + ‖B‖ * (δ * dist x y + Df) :=
      add_le_add (hgb (f x) (f y))
        ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hfb x y) (norm_nonneg B)))
    _ ≤ (δ * (L * dist x y + C) + Dg) + ‖B‖ * (δ * dist x y + Df) := by
      gcongr
      exact hfLip x y
    _ ≤ ε * dist x y + (δ * C + Dg + ‖B‖ * Df) := by
      nlinarith [mul_le_mul_of_nonneg_right hslope (dist_nonneg (x := x) (y := y))]

/-- A map a bounded distance from the identity cannot have a different
linear height coefficient modulo a sublinear two-point error. -/
theorem sublinear_linear_height_error_of_close_to_id
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (height : X → W) (f : X → X) (A : W →L[ℝ] W)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hheight : ∀ x y, ‖height x - height y‖ ≤ K * dist x y)
    (hclose : ∀ x, dist (f x) x ≤ C)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (f y) - height (f x) - A (height y - height x)‖ ≤ ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖(height y - height x) - A (height y - height x)‖ ≤ ε * dist x y + D := by
  intro ε hε
  obtain ⟨D, hD, hb⟩ := hf ε hε
  refine ⟨D + 2 * K * C, by positivity, ?_⟩
  intro x y
  have hy : ‖height y - height (f y)‖ ≤ K * C := by
    rw [norm_sub_rev]
    exact (hheight (f y) y).trans (mul_le_mul_of_nonneg_left (hclose y) hK)
  have hx := (hheight (f x) x).trans (mul_le_mul_of_nonneg_left (hclose x) hK)
  have he : (height y - height x) - A (height y - height x) =
      (height y - height (f y)) +
      (height (f y) - height (f x) - A (height y - height x)) +
      (height (f x) - height x) := by abel
  rw [he]
  have hn := (norm_add_le (height y - height (f y) +
    (height (f y) - height (f x) - A (height y - height x)))
    (height (f x) - height x)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  exact hn.trans (by linarith [hb x y])

/-- Actual linearly growing height rays identify a linear map whose height
error is sublinear. This is used for the two coarse-inverse coefficients. -/
theorem linear_height_coefficient_eq_id
    {X W : Type} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (base : X) (height : X → W) (A : W →L[ℝ] W) (ray : W → ℝ → X)
    (hray : ∀ w t, height (ray w t) - height base = t • w)
    (hmetric : ∀ w, ∃ L C : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 ≤ t → dist base (ray w t) ≤ L * t + C)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ x,
      ‖(height x - height base) - A (height x - height base)‖ ≤ ε * dist base x + D) :
    A = ContinuousLinearMap.id ℝ W := by
  ext w
  have hz : ‖w - A w‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖w - A w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    obtain ⟨L, C, hL, hm⟩ := hmetric w
    obtain ⟨R, hR⟩ := sublinear_error_on_linear_ray base
      (fun x => (height x - height base) - A (height x - height base)) (ray w) hsub hL hm
      (‖w - A w‖ / 2) (half_pos hp)
    let t := max R 1
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hh := hR t (le_max_left _ _) ht.le
    rw [hray, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hh
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanInverseCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse inverses have inverse linear height coefficients -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- Comparing the composition to the identity on the actual Cartan height
rays identifies the coefficients. No inverse relation is assumed. -/
theorem inverse_coefficients_of_sublinear_height
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (f g : G → G) (A B : W →L[ℝ] W)
    {K L C D : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hfLip : ∀ x y, dist (f x) (f y) ≤ L * dist x y + C)
    (hinv : ∀ x, dist (g (f x)) x ≤ D)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ E : ℝ, 0 ≤ E ∧ ∀ x y,
      ‖(π (f y)).toAdd - (π (f x)).toAdd - A ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + E)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ E : ℝ, 0 ≤ E ∧ ∀ x y,
      ‖(π (g y)).toAdd - (π (g x)).toAdd - B ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + E) :
    B.comp A = ContinuousLinearMap.id ℝ W := by
  have hcomp := two_point_sublinear_height_comp (fun x => (π x).toAdd)
    f g A B hL hC hfLip hf hg
  have hid := sublinear_linear_height_error_of_close_to_id (fun x => (π x).toAdd)
    (fun x => g (f x)) (B.comp A) hK hD hπ hinv hcomp
  obtain ⟨M, hM, hm⟩ := F.exists_heightRay_metric_bound T eW chartD hchartD
  apply linear_height_coefficient_eq_id (1 : G) (fun x => (π x).toAdd) (B.comp A)
    (fun w t => F.inclusionD (F.heightRay T eW w t))
  · intro w t
    rw [F.heightRay_height T eW π hπExp, map_one]
    simp
  · intro w
    refine ⟨M * ‖w‖, M, mul_nonneg hM (norm_nonneg _), ?_⟩
    intro t ht
    have hh := hm w t
    rw [abs_of_nonneg ht] at hh
    nlinarith
  · intro ε hε
    obtain ⟨E, _, he⟩ := hid ε hε
    exact ⟨E, fun x => he 1 x⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedPairInverseLabels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse coefficients for the actual normalized quasi-inverse pairs -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [IsTopologicalGroup G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- The inverse normalization only left-translates the inverse map, which
cancels in two-point height differences. Thus the proved sublinear labels
of the normalized pairs are genuinely inverse coefficients. -/
theorem normalized_pair_inverse_coefficients
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W →L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) (p : NormalizedPair G Λ) :
    (A (pairChartTransition (1, p)).1).comp (A p) = ContinuousLinearMap.id ℝ W := by
  let q := (pairChartTransition (1, p)).1
  have hheight x y : (π (x⁻¹ * y)).toAdd = (π y).toAdd - (π x).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
    abel
  have hs (r : NormalizedPair G Λ) (ε : ℝ) (hε : 0 < ε) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖(π (r.val.1 y)).toAdd - (π (r.val.1 x)).toAdd - A r ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + D := by
    obtain ⟨D, hD, hb⟩ := hsub ε hε
    exact ⟨D, hD, fun x y => by simpa only [hheight] using hb r x y⟩
  have hq x y : (π (q.val.1 y)).toAdd - (π (q.val.1 x)).toAdd =
      (π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd := by
    dsimp only [q]
    simp only [pairChartTransition_forward, inv_one, one_mul, map_mul, map_inv,
      toAdd_mul, toAdd_inv]
    abel
  apply F.inverse_coefficients_of_sublinear_height T eW π hπExp chartD hchartD
    p.val.1 p.val.2 (A p) (A q) hK Λ.coe_nonneg (show 0 ≤ (0 : ℝ) from le_rfl)
    Λ.coe_nonneg hπ
  · intro x y
    simpa only [add_zero] using p.property.1.1.dist_le_mul x y
  · exact p.property.1.2.2.2.2.1
  · exact hs p
  · intro ε hε
    obtain ⟨D, hD, hb⟩ := hs q ε hε
    exact ⟨D, hD, fun x y => by simpa only [hq] using hb x y⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportDirectionCap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating one unsupported direction by a small cap

The cap preserves all the supports in a finite list of directions and
strictly lowers support in a direction outside their positive rays.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I]

/-- A compact convex truncation of the unit ball leaves the prescribed
support values unchanged but strictly lowers support in any additional
direction not on their positive rays. -/
theorem exists_support_direction_cap (v : I → W) (b : W) (hb : b ≠ 0)
    (hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i) :
    ∃ E : Set W, IsCompact E ∧ E.Nonempty ∧ Convex ℝ E ∧
      E ⊆ Metric.closedBall 0 1 ∧
      (∀ i, ∃ x ∈ E, inner ℝ (v i) x = ‖v i‖) ∧
      ∃ c : ℝ, c < ‖b‖ ∧ ∀ x ∈ E, inner ℝ b x ≤ c := by
  classical
  let u : I → W := fun i => ‖v i‖⁻¹ • v i
  have hunorm (i : I) : ‖u i‖ ≤ 1 := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [u, norm_smul, hvn]
  have huinner (i : I) : inner ℝ (v i) (u i) = ‖v i‖ := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
  have hult (i : I) : inner ℝ b (u i) < ‖b‖ := by
    by_cases hv : v i = 0
    · simpa [u, hv] using norm_pos_iff.mpr hb
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hunit : ‖u i‖ = 1 := by
        simp [u, norm_smul, hvn]
      have hne : ‖u i‖ • b ≠ ‖b‖ • u i := by
        intro heq
        have heq' : b = (‖b‖ / ‖v i‖) • v i := by
          simpa only [hunit, one_smul, u, smul_smul, div_eq_mul_inv] using heq
        exact hnot i (‖b‖ / ‖v i‖)
          (div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv)) heq'
      simpa only [hunit, mul_one] using (inner_lt_norm_mul_iff_real.mpr hne)
  let x : Option I → W := fun i => i.elim 0 u
  let c : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Option I => inner ℝ b (x i))
  have hc0 : 0 ≤ c := by
    have hh := Finset.le_sup' (f := fun i : Option I => inner ℝ b (x i))
      (Finset.mem_univ none)
    simpa only [x, Option.elim_none, inner_zero_right] using hh
  have hcb : c < ‖b‖ := by
    rw [Finset.sup'_lt_iff]
    intro i _
    cases i with
    | none => simpa only [x, Option.elim_none, inner_zero_right] using norm_pos_iff.mpr hb
    | some i => exact hult i
  let E := Metric.closedBall (0 : W) 1 ∩ {y : W | inner ℝ b y ≤ c}
  have hclosed : IsClosed {y : W | inner ℝ b y ≤ c} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcompact : IsCompact E := (isCompact_closedBall (0 : W) 1).inter_right hclosed
  have hconvex : Convex ℝ E := (convex_closedBall (0 : W) 1).inter
    (convex_halfSpace_le (innerSL ℝ b).toLinearMap.isLinear c)
  refine ⟨E, hcompact, ⟨0, ?_⟩, hconvex, inter_subset_left, ?_, c, hcb, ?_⟩
  · exact ⟨by simp, by simpa using hc0⟩
  · intro i
    refine ⟨u i, ⟨?_, ?_⟩, huinner i⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hunorm i
    · exact Finset.le_sup' (f := fun j : Option I => inner ℝ b (x j))
        (Finset.mem_univ (some i))
  · exact fun _ hy => hy.2

end PolycyclicRecognition

end

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

omit [FiniteDimensional ℝ W] in
theorem basisTemplateSupport_le (E : Set W) (b : B) :
    D.basisTemplateSupport E b ≤ D.templateSupport E :=
  Finset.le_sup' (f := D.basisTemplateSupport E) (Finset.mem_univ b)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateSupportOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Monotonicity and strictness of the weighted template support -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set
open scoped BigOperators

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [Nonempty B] in
theorem weightSupport_eq_of_bound_and_attained {E : Set W} (hc : IsCompact E)
    (i : I) (r : ℝ) (hbound : ∀ x ∈ E, D.weight i x ≤ r)
    (hattained : ∃ x ∈ E, D.weight i x = r) : D.weightSupport E i = r := by
  obtain ⟨x, hx, heq⟩ := hattained
  apply le_antisymm
  · obtain ⟨y, hy, hsup⟩ := D.exists_weightSupport_point hc ⟨x, hx⟩ i
    rw [hsup]
    exact hbound y hy
  · rw [← heq]
    exact D.weight_le_weightSupport hc hx i

omit [Nonempty B] in
theorem weightSupport_mono {E F : Set W} (hE : IsCompact E) (hn : E.Nonempty)
    (hF : IsCompact F) (hEF : E ⊆ F) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i := by
  obtain ⟨x, hx, heq⟩ := D.exists_weightSupport_point hE hn i
  rw [heq]
  exact D.weight_le_weightSupport hF (hEF hx) i

omit [FiniteDimensional ℝ W] in
/-- Every word basis contains every generator with positive multiplicity,
so decreasing one support strictly decreases the entire finite maximum. -/
theorem templateSupport_lt_of_weightSupport {E F : Set W}
    (hle : ∀ i, D.weightSupport E i ≤ D.weightSupport F i)
    (hlt : ∃ i, D.weightSupport E i < D.weightSupport F i) :
    D.templateSupport E < D.templateSupport F := by
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  change Finset.univ.sup' _ _ < _
  rw [hb]
  apply lt_of_lt_of_le _ (D.basisTemplateSupport_le F b)
  unfold basisTemplateSupport
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg _)
  · obtain ⟨i, hi⟩ := hlt
    exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_left hi (Nat.cast_pos.mpr (D.positive b i))⟩

end PolycyclicRecognition.SupportDatum

end

end OAI
end

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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r132feb_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r132feb_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r132feb_2 : Nontrivial (rootSpace H χ) :=
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal contains every outside generalized weight space -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- For a pointed positive cone, the zero generalized weight space is
removed in the quotient. Here the allowed set omits the cone vertex. -/
theorem zero_genWeightSpace_le_coneWordIdeal
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C) :
    (genWeightSpace (cartanRootIdeal H) (0 : H → ℝ)).toSubmodule ≤
      (M.coneWordIdeal C).toSubmodule :=
  M.outside_genWeightSpace_le_coneWordIdeal C hadd 0 hzero

set_option maxHeartbeats 1000000 in
/-- In particular the Cartan/root intersection is killed by the cone
quotient, so the later action can descend through the factorization of G. -/
theorem cartan_intersection_mem_coneWordIdeal
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C) (v : cartanRootIdeal H) (hv : (v : L) ∈ H) :
    v ∈ M.coneWordIdeal C := by
  let ι : (cartanRootIdeal H) →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  have hroot : v ∈ genWeightSpace (cartanRootIdeal H) (0 : H → ℝ) := by
    rw [← comap_genWeightSpace_eq_of_injective (f := ι)
      ((cartanRootIdeal H).restr H).injective_incl]
    exact toLieSubmodule_le_rootSpace_zero ℝ L H hv
  exact M.zero_genWeightSpace_le_coneWordIdeal C hadd hzero hroot

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem zero_not_mem_positiveWeightRay {α : V} (hα : α ≠ 0) :
    (0 : V) ∉ positiveWeightRay α := by
  rintro ⟨c, hc, he⟩
  exact (smul_ne_zero (ne_of_gt hc) hα) he.symm

theorem positiveWeightRay_self (α : V) : α ∈ positiveWeightRay α :=
  ⟨1, zero_lt_one, (one_smul ℝ α).symm⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TemplateWeightRays
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template symmetries preserve the positive generator-weight rays -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The cap argument from the support-symmetries lemma: pullback of every
nonzero generator weight is a positive multiple of another generator weight.
It uses preservation of all compact convex templates, not only segments. -/
theorem templateSymmetry_weight_ray
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (r : ℝ), 0 < r ∧ (D.weight j).comp A.val.toLinearMap = r • D.weight i := by
  classical
  let v : I → W := fun i => (InnerProductSpace.toDual ℝ W).symm
    (D.weight i).toContinuousLinearMap
  let β : W →ₗ[ℝ] ℝ := (D.weight j).comp A.val.toLinearMap
  let b : W := (InnerProductSpace.toDual ℝ W).symm β.toContinuousLinearMap
  have hv (i : I) (x : W) : inner ℝ (v i) x = D.weight i x :=
    InnerProductSpace.toDual_symm_apply
  have hbval (x : W) : inner ℝ b x = D.weight j (A.val x) :=
    InnerProductSpace.toDual_symm_apply
  have hb : b ≠ 0 := by
    intro hb
    apply hj
    ext x
    have hh := hbval (A.val.symm x)
    simpa only [hb, inner_zero_left, LinearEquiv.apply_symm_apply, LinearMap.zero_apply]
      using hh.symm
  by_contra hn
  have hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i := by
    intro i r hr heq
    apply hn
    refine ⟨i, r, hr, ?_⟩
    ext x
    change D.weight j (A.val x) = r * D.weight i x
    rw [← hbval, heq, real_inner_smul_left, hv]
  obtain ⟨E, hE, hne, hconv, hEK, hreach, c, hcb, hcap⟩ :=
    exists_support_direction_cap v b hb hnot
  let K := Metric.closedBall (0 : W) 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hbound (i : I) (x : W) (hx : x ∈ K) : D.weight i x ≤ ‖v i‖ := by
    have hx' : ‖x‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    rw [← hv]
    exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (v i)])
  have hsupp (i : I) : D.weightSupport E i = D.weightSupport K i := by
    obtain ⟨x, hx, heq⟩ := hreach i
    have heq' : D.weight i x = ‖v i‖ := by rwa [hv] at heq
    have hsE := D.weightSupport_eq_of_bound_and_attained hE i ‖v i‖
      (fun y hy => hbound i y (hEK hy)) ⟨x, hx, heq'⟩
    have hsK := D.weightSupport_eq_of_bound_and_attained hK i ‖v i‖
      (hbound i) ⟨x, hEK hx, heq'⟩
    exact hsE.trans hsK.symm
  have hPE : D.templateSupport E = D.templateSupport K := by
    unfold SupportDatum.templateSupport
    congr 1
    funext k
    simp only [SupportDatum.basisTemplateSupport, hsupp]
  have hAE : IsCompact (A.val '' E) := hE.image A.val.continuous_of_finiteDimensional
  have hAK : IsCompact (A.val '' K) := hK.image A.val.continuous_of_finiteDimensional
  have hAEne : (A.val '' E).Nonempty := hne.image A.val
  have hle (i : I) : D.weightSupport (A.val '' E) i ≤ D.weightSupport (A.val '' K) i :=
    D.weightSupport_mono hAE hAEne hAK (image_mono hEK) i
  have hjE : D.weightSupport (A.val '' E) j ≤ c := by
    obtain ⟨_, ⟨x, hx, rfl⟩, heq⟩ := D.exists_weightSupport_point hAE hAEne j
    rw [heq, ← hbval]
    exact hcap x hx
  let u : W := ‖b‖⁻¹ • b
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have huK : u ∈ K := by
    simp [u, K, Metric.mem_closedBall, dist_zero_right, norm_smul, hbn]
  have hbu : inner ℝ b u = ‖b‖ := by
    simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hjK : ‖b‖ ≤ D.weightSupport (A.val '' K) j := by
    have hh := D.weight_le_weightSupport hAK (mem_image_of_mem A.val huK) j
    rw [← hbval, hbu] at hh
    exact hh
  have hstrict := D.templateSupport_lt_of_weightSupport hle
    ⟨j, hjE.trans_lt (hcb.trans_le hjK)⟩
  rw [A.property E hE hne hconv,
    A.property K hK hKne (convex_closedBall (0 : W) 1), hPE] at hstrict
  exact lt_irrefl _ hstrict

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cone quotient action for the actual overlapping Cartan factors -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  {EN N Q : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [Group Q]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
  (hExpN : IsGroupExponential ExpN) (hbij : Function.Bijective ExpN)
  (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
omit M T hExpN dynkin [FiniteDimensional ℝ L] [T2Space N] in
include hbij in
/-- In exponential coordinates the actual quotient kernel is exactly the
given linear ideal. -/
theorem mem_kernel_exp_iff
    (I : LieIdeal ℝ (cartanRootIdeal H)) (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (I : Set (cartanRootIdeal H))))
    (v : cartanRootIdeal H) : ExpN (eN v) ∈ π.ker ↔ v ∈ I := by
  change ExpN (eN v) ∈ (π.ker : Set N) ↔ v ∈ I
  rw [hker]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, he⟩
    exact eN.injective (hbij.injective he) ▸ hw
  · intro hv
    exact ⟨eN v, ⟨v, hv, rfl⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- The genuine adjoint group automorphism preserves the actual quotient
kernel. No extra invariance hypothesis about the group is required. -/
theorem cone_kernel_adjoint_invariant
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (h : H) (g : N) :
    M.adjointGroupAutomorphism T eN ExpN hExpN hbij dynkin h g ∈ π.ker ↔ g ∈ π.ker := by
  obtain ⟨v, rfl⟩ := (hbij.comp eN.bijective).surjective g
  change integrateNilpotentLieEquiv eN ExpN hbij dynkin hExpN M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (ExpN (eN v)) ∈ π.ker ↔ _
  rw [integrateNilpotentLieEquiv_apply_exp]
  change ExpN (eN (cartanIdealAdjointAutomorphism T H h v)) ∈ π.ker ↔
    ExpN (eN v) ∈ π.ker
  rw [mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker,
    mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker]
  exact M.coneWordIdeal_adjoint_mem_iff T C hadd h v

end CartanWordModel

section ActualFactors

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
/-- The already proved exact overlap of the actual factors is killed by
the cone quotient, because its logarithm is in the zero weight space. -/
theorem cartan_factor_overlap_killed
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q)
    (hπ : ∀ v : cartanRootIdeal H,
      π (F.ExpN (F.N.equiv v)) = 1 ↔ v ∈ M.coneWordIdeal C)
    (n : F.N.carrier) (d : F.D.carrier) (he : F.inclusionN n = F.inclusionD d) :
    π n = 1 := by
  have hg : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n, rfl⟩, ⟨d, he.symm⟩⟩
  rw [F.overlap] at hg
  obtain ⟨v, ⟨hvN, hvH⟩, hv⟩ := hg
  let x : cartanRootIdeal H := ⟨v, hvN⟩
  have hn : F.ExpN (F.N.equiv x) = n :=
    F.closedN.injective ((F.compatibleN x).trans hv)
  rw [← hn]
  exact (hπ x).mpr (M.cartan_intersection_mem_coneWordIdeal C hadd hzero x hvH)

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
include T in
/-- Faithful exponential compatibility identifies the actual factor action
with the adjoint automorphism, so its cone kernel invariance is derived. -/
theorem cartan_factor_cone_kernel_invariant
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : F.N.carrier →* Q)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (d : F.D.carrier) (n : F.N.carrier) : F.action d n ∈ π.ker ↔ n ∈ π.ker := by
  obtain ⟨h, rfl⟩ := (hDsurj.comp F.D.equiv.surjective) d
  have he : F.action (F.ExpD (F.D.equiv h)) n =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hNbij dynkin h n := by
    apply F.closedN.injective
    rw [F.conjugation]
    exact (M.adjointGroupAutomorphism_eq_conjugation T F.N.equiv F.ExpN F.isExpN hNbij
      dynkin j ρ hρ F.inclusionN (fun h => F.inclusionD (F.ExpD (F.D.equiv h))) hN hD h n).symm
  change F.action (F.ExpD (F.D.equiv h)) n ∈ π.ker ↔ n ∈ π.ker
  rw [he]
  exact M.cone_kernel_adjoint_invariant T F.N.equiv F.ExpN F.isExpN hNbij dynkin C hadd π hker h n

end ActualFactors
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeAmbientAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ambient action on the actual cone quotient

The algebraic ideal and its integrated kernel determine the action and its
stabilizer. No injective product decomposition of the ambient group is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G Q : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
include T in
/-- The constructed nilpotent quotient carries the ambient action in the
cone-quotient lemma, with exact equivariance and stabilizer. -/
theorem exists_cartan_cone_ambient_action
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q) (s : Q → F.N.carrier) (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H)))) :
    ∃ (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q),
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ F.inclusionN n * F.inclusionD d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have ha := cartan_factor_cone_kernel_invariant M F T j ρ hρ hN hD hNbij hDsurj
    dynkin C hadd π hker
  have hkill : ∀ n d, F.inclusionN n = F.inclusionD d → π n = 1 := by
    apply cartan_factor_overlap_killed M F C hadd hzero π
    intro v
    exact CartanWordModel.mem_kernel_exp_iff F.N.equiv F.ExpN hNbij (M.coneWordIdeal C) π hker v
  obtain ⟨act, hact, hstab, heq⟩ := exists_descended_factor_quotient_action
    F.inclusionN F.inclusionD F.closedN.injective F.action F.conjugation F.surjective
    π s hs ha hkill
  exact ⟨descendQuotientAction π s hs F.action ha, act,
    descendQuotientAction_project π s hs F.action ha, hact, hstab, heq⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRayBoundaryModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

variable [SimplyConnectedSpace G] {a : ℕ}
  (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000 in
include T in
/-- No boundary or metric conclusion is assumed in the construction. -/
theorem nonempty_rayBoundaryModel_of_published_inputs
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (inputs : M.PolarConeModelInputs F (positiveWeightRay α₀)) (hα₀ : α₀ ≠ 0) :
    Nonempty (M.RayBoundaryModel F α₀) := by
  let C := inputs.model M F (positiveWeightRay α₀) T hExpG realize haarN
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨α, act, hα, hact, hstab, _⟩ := exists_cartan_cone_ambient_action M F T
    j ρ hρ (fun v => by rw [F.compatibleN, hmatch])
    (fun v => by rw [F.compatibleD, hmatch]) hbijN hbijD.surjective dynkinN
    (positiveWeightRay α₀) (positiveWeightRay_add α₀)
    (zero_not_mem_positiveWeightRay hα₀)
    C.maps.quotient C.maps.sectionMap C.maps.section_rightInverse C.maps.kernel_eq
  exact ⟨⟨C, α, act, hα, hact, hstab⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryRayMatching
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The missing generator ray for each template symmetry -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

local notation "α" => SupportDatum.weight (supportIn M T hunimod eW)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ W] in
/-- The original Cartan generator characters are exactly the pullbacks of
the chosen Euclidean height coordinates. -/
theorem support_weight_comp_height (j : Fin M.letterCount) :
    (α j).comp θ = (M.weight j : H →ₗ[ℝ] ℝ) := by
  ext h
  change cartanHeightWeight T H (M.weight j)
    (eW.symm (eW (heightProjection T.character (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) = _
  rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundaryRetainedRay
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retained generators and negative height directions for the actual rays -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

local notation "α" => SupportDatum.weight (supportIn M T hunimod eW)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))

set_option maxHeartbeats 1000000 in
/-- A pulled-back target weight retains a genuine source generator. This
supplies both the nonzero ray needed for the descended action and the strict
positivity of its Haar character. -/
theorem exists_retained_generator_for_template_ray
    (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount) :
    let χ := ((α i).comp A.val.toLinearMap).comp θ
    χ ≠ 0 ∧ ∃ j : Fin M.letterCount,
      (M.weight j : H →ₗ[ℝ] ℝ) ∈ positiveWeightRay χ := by
  have hn : α i ≠ 0 := by
    intro hz
    exact M.sampling_weight_ne_zero T hunimod eW i
      (congrArg LinearMap.toContinuousLinearMap hz)
  obtain ⟨j, r, hr, he⟩ := templateSymmetry_weight_ray (M.supportIn T hunimod eW) A i hn
  have hsource : ((α i).comp A.val.toLinearMap).comp θ = r • (M.weight j : H →ₗ[ℝ] ℝ) := by
    rw [he, LinearMap.smul_comp, M.support_weight_comp_height T hunimod eW j]
  have hnj : (M.weight j : H →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hj
    apply M.weight_nonzero j
    funext h
    exact LinearMap.congr_fun hj h
  refine ⟨?_, j, r⁻¹, inv_pos.mpr hr, ?_⟩
  · rw [hsource]
    exact smul_ne_zero hr.ne' hnj
  · rw [hsource, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

set_option maxHeartbeats 1000000 in
/-- The selected nonzero target weight has a contracting direction in
height space. -/
theorem exists_negative_sampling_weight (i : Fin M.letterCount) :
    ∃ w : W, α i w < 0 := by
  have hn : α i ≠ 0 := by
    intro hz
    exact M.sampling_weight_ne_zero T hunimod eW i
      (congrArg LinearMap.toContinuousLinearMap hz)
  have hex : ∃ w : W, α i w ≠ 0 := by
    by_contra h
    apply hn
    ext w
    exact not_ne_iff.mp (not_exists.mp h w)
  obtain ⟨w, hw⟩ := hex
  by_cases hneg : α i w < 0
  · exact ⟨w, hneg⟩
  · exact ⟨-w, by rw [map_neg]; exact neg_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hw))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSublinearRayComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing one boundary comparison from the published inputs and sublinear height -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

variable (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)

local notation "αT" => LinearMap.toContinuousLinearMap (SupportDatum.weight (supportIn M T hunimod eW) i)
local notation "A₀" => LinearEquiv.toContinuousLinearEquiv (Subtype.val A)
local notation "αS" => ContinuousLinearMap.comp αT (ContinuousLinearEquiv.toContinuousLinearMap A₀)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))
local notation "χS" => LinearMap.comp (ContinuousLinearMap.toLinearMap αS) θ
local notation "χT" => LinearMap.comp (ContinuousLinearMap.toLinearMap αT) θ

set_option maxHeartbeats 1000000 in
include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- All ray models, actions, boundary maps, and volume comparisons are
constructed here. Only the previously established sublinear estimates and
precisely stated published Lie inputs enter the construction. -/
theorem exists_published_boundary_comparison_of_sublinear
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : M.PolarConeModelInputs F (positiveWeightRay χS))
    (targetInputs : M.PolarConeModelInputs F (positiveWeightRay χT))
    (sourceDynkin : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay χS)), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay χT)), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (f g : P → G → G) (hfcont : ∀ p, Continuous (f p)) (hgcont : ∀ p, Continuous (g p))
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (hsubf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((f p x)⁻¹ * f p (x * y))).toAdd - A.val ((height y).toAdd)‖ ≤ ε * dist 1 y + B)
    (hsubg : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((g p x)⁻¹ * g p (x * y))).toAdd - A.val.symm ((height y).toAdd)‖ ≤ ε * dist 1 y + B) :
    ∃ (RS : M.RayBoundaryModel F χS) (RT : M.RayBoundaryModel F χT),
      Nonempty (RayBoundaryComparison RS RT height f) := by
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  have hbijD : Function.Bijective F.ExpD := by
    rw [← show chartD = F.ExpD from funext hchartD]
    exact chartD.bijective
  obtain ⟨hχS, jS, hjS⟩ := M.exists_retained_generator_for_template_ray T hunimod eW A i
  have hχT : χT = (M.weight i : H →ₗ[ℝ] ℝ) := M.support_weight_comp_height T hunimod eW i
  have hχTne : χT ≠ 0 := by
    rw [hχT]
    intro hz
    apply M.weight_nonzero i
    funext h
    exact LinearMap.congr_fun hz h
  let RS : M.RayBoundaryModel F χS := Classical.choice <|
    M.nonempty_rayBoundaryModel_of_published_inputs F χS T hExpG realize haarN
      hbijN hbijD dynkinN sourceInputs hχS
  let RT : M.RayBoundaryModel F χT := Classical.choice <|
    M.nonempty_rayBoundaryModel_of_published_inputs F χT T hExpG realize haarN
      hbijN hbijD dynkinN targetInputs hχTne
  obtain ⟨w, hw⟩ := M.exists_negative_sampling_weight T hunimod eW i
  have hv : αS ((A₀).symm w) < 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, LinearMap.coe_toContinuousLinearMap'] using hw
  obtain ⟨B, KS, KT, hKS, hKT, hB, hC⟩ := M.exists_ray_boundary_family_homeomorphisms
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip αS αT A₀ rfl RS RT
    (sourceDynkin RS.cone.Q) (targetDynkin RT.cone.Q)
    f g hfcont hgcont hLf hLg hf hg hgf hfg hsubf hsubg ((A₀).symm w) hv
  refine ⟨RS, RT, ?_⟩
  exact nonempty_rayBoundaryComparison_of_shadows_m RS RT height f hExpG realize hbijN hbijD
    dynkinN (sourceInputs.haarQ RS.cone.Q) (targetInputs.haarQ RT.cone.Q) hheight
    jS i hjS (by rw [hχT]; exact positiveWeightRay_self _)
    B g hLf hLg hf hg hgf KS KT hKS hKT hB hC

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSublinearBoundedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded height for a fixed template from published Lie inputs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W P : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)


variable (A : templateSymmetryGroup (M.supportIn T hunimod eW))

local notation "αT" => fun i => LinearMap.toContinuousLinearMap (SupportDatum.weight (supportIn M T hunimod eW) i)
local notation "A₀" => LinearEquiv.toContinuousLinearEquiv (Subtype.val A)
local notation "αS" => fun i => ContinuousLinearMap.comp (αT i) (ContinuousLinearEquiv.toContinuousLinearMap A₀)
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))
local notation "χS" => fun i => LinearMap.comp (ContinuousLinearMap.toLinearMap (αS i)) θ
local notation "χT" => fun i => LinearMap.comp (ContinuousLinearMap.toLinearMap (αT i)) θ

set_option maxHeartbeats 1000000 in
include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- Boundary comparisons are constructed from the published inputs, so the
fixed-label bounded estimate no longer assumes any boundary data. -/
theorem uniform_affine_bound_of_published_inputs_and_sublinear
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (χS i)))
    (targetInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (χT i)))
    (sourceDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (χS i)))), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (χT i)))), NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (f g : P → G → G) (hfcont : ∀ p, Continuous (f p)) (hgcont : ∀ p, Continuous (g p))
    {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (hsubf : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((f p x)⁻¹ * f p (x * y))).toAdd - A.val ((height y).toAdd)‖ ≤ ε * dist 1 y + B)
    (hsubg : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height ((g p x)⁻¹ * g p (x * y))).toAdd - A.val.symm ((height y).toAdd)‖ ≤ ε * dist 1 y + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
      ‖(height (f p x)).toAdd - ((height (f p 1)).toAdd + A.val (height x).toAdd)‖ ≤ K := by
  classical
  have hex (i : Fin M.letterCount) := M.exists_published_boundary_comparison_of_sublinear
    T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD A i
    hExpG realize haarN haarD b₀ γ₀ hpath hKheight hLip
    (sourceInputs i) (targetInputs i) (sourceDynkin i) (targetDynkin i)
    f g hfcont hgcont hLf hLg hf hg hgf hfg hsubf hsubg
  choose RS RT hC using hex
  let C := fun i => Classical.choice (hC i)
  have hbijN : Function.Bijective F.ExpN := by
    rw [← show chartN = F.ExpN from funext hchartN]
    exact chartN.bijective
  apply M.uniform_affine_bound_of_boundary_comparisons T F hunimod eW height f A
    RS RT C hExpG realize hbijN chartD hchartD dynkinN metricInput
    (fun i => sourceDynkin i (RS i).cone.Q)
    (fun i => (sourceInputs i).haarQ (RS i).cone.Q) hheight haarN b₀ γ₀
  intro p ε hε
  obtain ⟨B, _, hb⟩ := hsubf ε hε
  refine ⟨B, fun x => ?_⟩
  have h := hb p 1 x
  simpa only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv, neg_add_eq_sub] using h

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedPairBackwardHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform height estimates for the actual backward maps -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [IsTopologicalGroup G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- The already proved inverse-coefficient identity determines the inverse
linear equivalence, including the normalization translation. -/
theorem normalized_pair_inverse_equiv
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W ≃L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) (p : NormalizedPair G Λ) :
    A (pairChartTransition (1, p)).1 = (A p).symm := by
  have h := F.normalized_pair_inverse_coefficients T eW π hπExp chartD hchartD
    (fun q => (A q).toContinuousLinearMap) hK hπ hsub p
  apply ContinuousLinearEquiv.ext
  funext w
  have he := congrArg (fun f : W →L[ℝ] W => f ((A p).symm w)) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using he

/-- The backward maps inherit the same uniform two-point error, with the
inverse coefficient. Left normalization cancels exactly in their heights. -/
theorem normalized_pair_backward_sublinear_height
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W ≃L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd - (A p).symm ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D := by
  intro ε hε
  obtain ⟨D, hD, hb⟩ := hsub ε hε
  refine ⟨D, hD, ?_⟩
  intro p x y
  let q := (pairChartTransition (1, p)).1
  have hq := F.normalized_pair_inverse_equiv T eW π hπExp chartD hchartD A hK hπ hsub p
  have he : (π (q.val.1 y)).toAdd - (π (q.val.1 x)).toAdd =
      (π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd := by
    dsimp only [q]
    simp only [pairChartTransition_forward, inv_one, one_mul, map_mul, map_inv,
      toAdd_mul, toAdd_inv]
    abel
  have hh := hb q x y
  rw [he, show A q = (A p).symm from hq] at hh
  exact hh

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNormalizedBoundedHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounded height over all normalized pairs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal BigOperators

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)



local notation "D" => supportIn M T hunimod eW
local notation "θ" => LinearMap.comp (LinearEquiv.toLinearMap eW)
  (LinearMap.comp (heightProjection (TriangularAdjoint.character T))
    (Submodule.subtype (LieSubalgebra.toSubmodule H)))

set_option maxHeartbeats 1000000 in
include hheight chartN hchartN chartD hchartD dynkinN dynkinD in
/-- Finite template labels turn the published-input fixed-label bounds into
one bound for every normalized pair. The backward estimate is derived from
the forward estimate by the actual inverse normalization identity. -/
theorem uniform_normalized_affine_bound_of_published_inputs_and_sublinear_oai
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (metricInput : GeodesicMetricExistenceInput)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (sourceInputs : ∀ (A : templateSymmetryGroup D) i,
      M.PolarConeModelInputs F (positiveWeightRay ((((D).weight i).comp A.val.toLinearMap).comp θ)))
    (targetInputs : ∀ i, M.PolarConeModelInputs F (positiveWeightRay (((D).weight i).comp θ)))
    (sourceDynkin : ∀ (A : templateSymmetryGroup D) i
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
        M.coneWordIdeal (positiveWeightRay ((((D).weight i).comp A.val.toLinearMap).comp θ)))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (targetDynkin : ∀ i (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (positiveWeightRay (((D).weight i).comp θ)))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
      ‖(height (p.val.1 y)).toAdd - (height (p.val.1 x)).toAdd -
        (label p).val ((height (x⁻¹ * y)).toAdd)‖ ≤ ε * dist x y + B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
      ‖(height (p.val.1 x)).toAdd - (label p).val (height x).toAdd‖ ≤ K := by
  classical
  let : Fintype (templateSymmetryGroup D) := Fintype.ofFinite _
  have hback := F.normalized_pair_backward_sublinear_height T eW height hheight
    chartD hchartD (fun p => (label p).val.toContinuousLinearEquiv) hKheight hLip hsub
  have hfiber (A : templateSymmetryGroup D) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ (p : {p : NormalizedPair G Λ // label p = A}) x,
        ‖(height (p.val.val.1 x)).toAdd - A.val (height x).toAdd‖ ≤ K := by
    obtain ⟨K, hK, hb⟩ := M.uniform_affine_bound_of_published_inputs_and_sublinear (ef := 0) (eg := 0)
      T F hunimod eW height hheight chartN hchartN chartD hchartD dynkinN dynkinD A
      hExpG realize haarN haarD metricInput b₀ γ₀ hpath hKheight hLip
      (sourceInputs A) targetInputs (sourceDynkin A) targetDynkin
      (fun p : {p : NormalizedPair G Λ // label p = A} => p.val.val.1)
      (fun p => p.val.val.2)
      (fun p => p.val.val.1.continuous) (fun p => p.val.val.2.continuous)
      Λ.coe_nonneg Λ.coe_nonneg
      (fun p x y => by simpa only [add_zero] using p.val.property.1.1.dist_le_mul x y)
      (fun p x y => by simpa only [add_zero] using p.val.property.1.2.1.dist_le_mul x y)
      (fun p => p.val.property.1.2.2.2.2.1) (fun p => p.val.property.1.2.2.2.2.2)
      (by
        intro ε hε
        obtain ⟨B, hB, hb⟩ := hsub ε hε
        refine ⟨B, hB, ?_⟩
        intro p x y
        have h := hb p.val x (x * y)
        rw [show dist x (x * y) = dist 1 y by simpa only [mul_one] using dist_mul_left x (1 : G) y] at h
        simpa only [p.property, inv_mul_cancel_left, dist_mul_left, map_mul, map_inv,
          toAdd_mul, toAdd_inv, neg_add_eq_sub] using h)
      (by
        intro ε hε
        obtain ⟨B, hB, hb⟩ := hback ε hε
        refine ⟨B, hB, ?_⟩
        intro p x y
        have h := hb p.val x (x * y)
        rw [show dist x (x * y) = dist 1 y by simpa only [mul_one] using dist_mul_left x (1 : G) y] at h
        simpa only [p.property, inv_mul_cancel_left, dist_mul_left, map_mul, map_inv,
          toAdd_mul, toAdd_inv, neg_add_eq_sub, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_toContinuousLinearEquiv_symm'] using h)
    refine ⟨K, hK, fun p x => ?_⟩
    simpa only [p.val.property.2, map_one, toAdd_one, zero_add] using hb p x
  choose K hK hb using hfiber
  refine ⟨∑ A, K A, Finset.sum_nonneg (fun A _ => hK A), ?_⟩
  intro p x
  exact (hb (label p) ⟨p, rfl⟩ x).trans
    (Finset.single_le_sum (fun A _ => hK A) (Finset.mem_univ (label p)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear_oai := @OAI.PolycyclicRecognition.CartanWordModel.uniform_normalized_affine_bound_of_published_inputs_and_sublinear_oai
