-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:21:27.333553+00:00
-- url     : https://prove2.me/submissions/5bcf99cb-2ada-44c1-b3eb-6e65cfe6d853

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_invertible_height_factor_of_stationary_mean
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_templateSupport_le_of_stationary_height_factor_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CocycleGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sublinear cocycle bounds from compact coboundary approximation

Compact-uniform approximation by coboundaries makes an isometric cocycle
sublinear on words of linearly bounded length.
-/

namespace PolycyclicRecognition

variable {G E : Type} [Group G] [NormedAddCommGroup E]
  [DistribMulAction G E] [IsIsometricSMul G E]

theorem norm_isometric_action (g : G) (v : E) : ‖g • v‖ = ‖v‖ := by
  simpa only [smul_zero, dist_zero_right] using dist_smul g v (0 : E)

omit [IsIsometricSMul G E] in
/-- Coboundary correction preserves the cocycle identity. -/
theorem IsCocycle.corrected {b : G → E} (hb : IsCocycle b) (φ : E) :
    IsCocycle (fun g => b g + g • φ - φ) := by
  intro g h
  dsimp only
  rw [hb g h, mul_smul, smul_sub, smul_add]
  abel

theorem IsCocycle.norm_word_le {b : G → E} (hb : IsCocycle b)
    (Q : Set G) {ε : ℝ} (hQ : ∀ g ∈ Q, ‖b g‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) : ‖b l.prod‖ ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => simp [hb.map_one]
  | cons g l ih =>
    have htail : ∀ h ∈ l, h ∈ Q := fun h hh => hl h (by simp [hh])
    calc
      ‖b (g :: l).prod‖ = ‖b g + g • b l.prod‖ := by rw [List.prod_cons, hb g l.prod]
      _ ≤ ‖b g‖ + ‖g • b l.prod‖ := norm_add_le _ _
      _ = ‖b g‖ + ‖b l.prod‖ := by rw [norm_isometric_action]
      _ ≤ ε + (l.length : ℝ) * ε := add_le_add (hQ g (hl g (by simp))) (ih htail)
      _ = ((g :: l).length : ℝ) * ε := by simp [add_mul] <;> ring

/-- The error of removing a coboundary is at most twice the vector norm,
uniformly over the acting group. -/
theorem norm_le_corrected_add (b : G → E) (φ : E) (g : G) :
    ‖b g‖ ≤ ‖b g + g • φ - φ‖ + 2 * ‖φ‖ := by
  have heq : b g = (b g + g • φ - φ) - g • φ + φ := by abel
  calc
    ‖b g‖ = ‖(b g + g • φ - φ) - g • φ + φ‖ := congrArg norm heq
    _ ≤ ‖(b g + g • φ - φ) - g • φ‖ + ‖φ‖ := norm_add_le _ _
    _ ≤ (‖b g + g • φ - φ‖ + ‖g • φ‖) + ‖φ‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by rw [norm_isometric_action]; ring

/-- The concrete word estimate used after reduced cohomology vanishing. The
approximating vector is fixed before the word length tends to infinity. -/
theorem IsCocycle.norm_word_le_of_coboundary {b : G → E} (hb : IsCocycle b)
    (Q : Set G) (φ : E) {ε : ℝ}
    (hQ : ∀ g ∈ Q, ‖b g + g • φ - φ‖ ≤ ε)
    (l : List G) (hl : ∀ g ∈ l, g ∈ Q) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * ε + 2 * ‖φ‖ :=
  (norm_le_corrected_add b φ l.prod).trans
    (add_le_add ((hb.corrected φ).norm_word_le Q hQ l hl) le_rfl)

/-- Compact-uniform coboundary approximation implies a global sublinear
estimate. The length and word-factorization hypotheses are explicit. -/
theorem IsCocycle.sublinear_of_coboundary_approximation
    {b : G → E} (hb : IsCocycle b) (Q : Set G) (length : G → ℝ)
    (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  intro ε hε
  let δ := ε / (a + 1)
  have hden : 0 < a + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨φ, hφ⟩ := happrox δ hδ
  have hcoef : a * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  refine ⟨a * δ + 2 * ‖φ‖, by positivity, ?_⟩
  intro g
  obtain ⟨l, hl, hprod, hlbound⟩ := hword g
  calc
    ‖b g‖ = ‖b l.prod‖ := by rw [hprod]
    _ ≤ (l.length : ℝ) * δ + 2 * ‖φ‖ := hb.norm_word_le_of_coboundary Q φ hφ l hl
    _ ≤ (a * length g + a) * δ + 2 * ‖φ‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hlbound hδ.le) le_rfl
    _ = (a * δ) * length g + (a * δ + 2 * ‖φ‖) := by ring
    _ ≤ ε * length g + (a * δ + 2 * ‖φ‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (hlen g)) le_rfl

omit [Group G] [DistribMulAction G E] [IsIsometricSMul G E] in
/-- A global sublinear estimate is uniform after division by scale on every
linearly growing metric ball. The additive error is chosen before the scale. -/
theorem uniform_sublinear_on_balls {b : G → E} (length : G → ℝ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B)
    {R : ℝ} (hR : 0 ≤ R) : ∀ ε : ℝ, 0 < ε →
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ g, length g ≤ R * r → ‖b g‖ ≤ ε * r := by
  intro ε hε
  have hden : 0 < 2 * (R + 1) := by linarith
  let δ := ε / (2 * (R + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨B, hB, hb⟩ := hsub δ hδ
  refine ⟨2 * B / ε, by positivity, ?_⟩
  intro r hr g hg
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 2 * B / ε).trans hr
  have hBr : 2 * B ≤ r * ε := (div_le_iff₀ hε).mp hr
  have hcoef : δ * R ≤ ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ‖b g‖ ≤ δ * length g + B := hb g
    _ ≤ δ * (R * r) + B := add_le_add (mul_le_mul_of_nonneg_left hg hδ.le) le_rfl
    _ = (δ * R) * r + B := by ring
    _ ≤ (ε / 2) * r + B := add_le_add (mul_le_mul_of_nonneg_right hcoef hr0) le_rfl
    _ ≤ ε * r := by nlinarith

end PolycyclicRecognition

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

theorem pairSourceChart_forward (p : NormalizedPair G Λ) (x t : G) :
    (pairSourceChart (p, x)).val.1 t = p.val.2 (x * t) := by
  change p.val.2 (x⁻¹⁻¹ * t) = _
  rw [inv_inv]

theorem pairSourceChart_inverse (p : NormalizedPair G Λ) (x t : G) :
    (pairSourceChart (p, x)).val.2 t = x⁻¹ * p.val.1 t := rfl

theorem pairChartTransition_group (z : G) (p : NormalizedPair G Λ) :
    (pairChartTransition (z, p)).2 = (p.val.2 z⁻¹)⁻¹ := by
  change (p.val.2 (z⁻¹ * 1))⁻¹ = _
  rw [mul_one]

theorem pairChartTransition_forward (z : G) (p : NormalizedPair G Λ) (t : G) :
    (pairChartTransition (z, p)).1.val.1 t =
      (p.val.2 z⁻¹)⁻¹ * p.val.2 (z⁻¹ * t) := by
  change (p.val.2 (z⁻¹ * 1))⁻¹ * p.val.2 (z⁻¹ * (1 * t)) = _
  simp only [mul_one, one_mul]

theorem pairChartTransition_inverse (z : G) (p : NormalizedPair G Λ) (t : G) :
    (pairChartTransition (z, p)).1.val.2 t =
      z * p.val.1 (p.val.2 z⁻¹ * t) := by
  change (1 : G)⁻¹ * (z * p.val.1 (p.val.2 (z⁻¹ * 1) * t)) = _
  simp only [mul_one, inv_one, one_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCoupling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance of the pair coupling

The two commuting translations are written in both product charts. Haar
measure times the stationary probability gives the actual invariant coupling.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- The transition conjugates domain translation to right translation on the
second coordinate of the inverse chart. -/
theorem pairChartTransition_domain (x : G) (q : G × NormalizedPair G Λ) :
    pairChartTransition (pairDomainTranslation x q) =
      ((pairChartTransition q).1, (pairChartTransition q).2 * x) := by
  rcases q with ⟨z, p⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
    · simp only [pairDomainTranslation, pairChartTransition_forward,
        normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
        inv_mul_cancel_left, mul_assoc]
      group
    · simp only [pairDomainTranslation, pairChartTransition_inverse,
        normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
        mul_assoc]
      group
  · simp only [pairDomainTranslation, pairChartTransition_group,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
      ]
    group

/-- The target action in inverse coordinates is a normalized translation and a
left translation depending on the inverse pair. -/
theorem pairSourceChart_target (y : G) (q : NormalizedPair G Λ × G) :
    pairSourceChart (pairInverseTargetTranslation y q) =
      targetTranslate y⁻¹ (pairSourceChart q) := by
  rcases q with ⟨p, x⟩
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
  · simp only [pairInverseTargetTranslation, pairSourceChart_forward,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk,
      targetTranslate, targetTranslatePair]
    congr 1
    group
  · simp only [pairInverseTargetTranslation, pairSourceChart_inverse,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk,
      targetTranslate, targetTranslatePair]
    group

/-- Target translation in the first chart. -/
theorem pairTargetChart_target (y : G) (q : G × NormalizedPair G Λ) :
    pairTargetChart (y * q.1, q.2) = targetTranslate y (pairTargetChart q) := by
  rcases q with ⟨z, p⟩
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
    simp [pairTargetChart, targetTranslate, targetTranslatePair, mul_assoc]

/-- Target translation conjugated through the change of product charts. -/
theorem pairChartTransition_target (y : G) (q : G × NormalizedPair G Λ) :
    pairChartTransition (y⁻¹ * q.1, q.2) =
      pairInverseTargetTranslation y (pairChartTransition q) := by
  apply pairSourceChart.injective
  rw [pairSourceChart_target]
  change pairSourceChart (pairSourceChart.symm (pairTargetChart (y⁻¹ * q.1, q.2))) =
    targetTranslate y⁻¹ (pairSourceChart (pairSourceChart.symm (pairTargetChart q)))
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, pairTargetChart_target]

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Haar preservation in the target chart follows directly from stationarity
and right invariance of Haar measure. -/
theorem measurePreserving_pairDomainTranslation
    (m : Measure G) [SFinite m] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (x : G) :
    MeasurePreserving (pairDomainTranslation x) (m.prod μ) (m.prod μ) := by
  have hT : MeasurePreserving (normalizedTranslate x) μ μ := by
    have h := measurePreserving_smul x⁻¹ μ
    change MeasurePreserving (fun p => normalizedTranslate (x⁻¹)⁻¹ p) μ μ at h
    simpa only [inv_inv] using h
  have hskew : MeasurePreserving
      (fun q : NormalizedPair G Λ × G =>
        (normalizedTranslate x q.1, q.2 * q.1.val.1 x))
      (μ.prod m) (μ.prod m) := by
    apply hT.skew_product (g := fun p z => z * p.val.1 x)
    · exact measurable_snd.mul
        (((continuous_eval_const x).comp continuous_fst.subtype_val.fst).measurable)
    · exact Filter.Eventually.of_forall fun p => map_mul_right_eq_self m (p.val.1 x)
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := m)).comp
    (hskew.comp (Measure.measurePreserving_swap (μ := m) (ν := μ)))
  exact h

/-- In the inverse chart, the coupling is right invariant in the group fiber. -/
theorem measurePreserving_inversePairCoupling_right
    (m : Measure G) [SFinite m] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (x : G) :
    MeasurePreserving (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x))
      (inversePairCoupling m μ) (inversePairCoupling m μ) := by
  have hmeas : Measurable (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x)) :=
    measurable_fst.prodMk (measurable_snd.mul_const x)
  refine ⟨hmeas, ?_⟩
  unfold inversePairCoupling
  rw [Measure.map_map hmeas pairChartTransition.continuous.measurable]
  have hcomp : (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x)) ∘
      pairChartTransition = pairChartTransition ∘ pairDomainTranslation x := by
    funext q
    exact (pairChartTransition_domain x q).symm
  rw [hcomp, ← Measure.map_map pairChartTransition.continuous.measurable
    (measurePreserving_pairDomainTranslation m μ x).measurable,
    (measurePreserving_pairDomainTranslation m μ x).map_eq]

/-- The same coupling is invariant under the target action in inverse
coordinates. -/
theorem measurePreserving_inversePairCoupling_target
    (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ] (y : G) :
    MeasurePreserving (pairInverseTargetTranslation y)
      (inversePairCoupling m μ) (inversePairCoupling m μ) := by
  have hmeas : Measurable (pairInverseTargetTranslation (Λ := Λ) y) := by
    apply Measurable.prodMk
    · have hc : Continuous (normalizedTranslate (Λ := Λ) y) := by
        have h : Continuous (fun p : NormalizedPair G Λ => y⁻¹ • p) :=
          continuous_const_smul y⁻¹
        change Continuous (fun p => normalizedTranslate (y⁻¹)⁻¹ p) at h
        simpa only [inv_inv] using h
      exact hc.measurable.comp measurable_fst
    · exact (((continuous_eval_const y).comp
        continuous_fst.subtype_val.fst).measurable.inv).mul measurable_snd
  apply MeasurePreserving.of_semiconj
    (pairChartTransition.continuous.measurable.measurePreserving (m.prod μ))
    ((measurePreserving_mul_left m y⁻¹).prod (MeasurePreserving.id μ))
    (pairChartTransition_target y) hmeas

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_HaarProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring a measure along Haar fibers

A measure finite on compact subsets of a compact section times a group,
and invariant under translations of the group coordinate, is a product.
The section measure is obtained by averaging over a set of positive finite
Haar measure, never by restricting to a single fiber.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G X : Type} [MeasurableSpace G] [MeasurableSpace X]
  (M : Measure (X × G))

theorem haarFiberSlice_apply {E : Set X} (_hE : MeasurableSet E)
    {B : Set G} (hB : MeasurableSet B) :
    haarFiberSlice M E B = M (E ×ˢ B) := by
  rw [haarFiberSlice, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

theorem haarSectionMeasure_apply (m : Measure G) {B : Set G} (_hB : MeasurableSet B)
    {E : Set X} (hE : MeasurableSet E) :
    haarSectionMeasure M m B E = M (E ×ˢ B) / m B := by
  rw [haarSectionMeasure, Measure.smul_apply, Measure.map_apply measurable_fst hE,
    Measure.restrict_apply (measurable_fst hE)]
  have hset : Prod.fst ⁻¹' E ∩ univ ×ˢ B = E ×ˢ B := by ext q; simp
  rw [hset, smul_eq_mul, mul_comm, div_eq_mul_inv]


variable [Group G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem haarFiberSlice_rightInvariant
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {E : Set X} (hE : MeasurableSet E) :
    (haarFiberSlice M E).IsMulRightInvariant := by
  constructor
  intro g
  ext B hB
  rw [Measure.map_apply (measurable_mul_const g) hB,
    haarFiberSlice_apply M hE ((measurable_mul_const g) hB),
    haarFiberSlice_apply M hE hB]
  exact (hM g).measure_preimage (hE.prod hB).nullMeasurableSet

/-- Right-invariant uniqueness, deduced from left-invariant uniqueness by
inverting both measures. -/
theorem rightInvariant_eq_div_smul (μ m : Measure G)
    [SigmaFinite μ] [SigmaFinite m] [μ.IsMulRightInvariant] [m.IsMulRightInvariant]
    {B : Set G} (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    μ = (μ B / m B) • m := by
  have h := MeasureTheory.measure_eq_div_smul μ.inv m.inv
    (s := B⁻¹) (by simpa using hB0) (by simpa using hBtop)
  have hi := congrArg (fun ρ : Measure G => ρ.inv) h
  simp only [Measure.inv_inv, Measure.inv_apply, inv_inv] at hi
  rw [Measure.inv, Measure.map_smul] at hi
  change μ = (μ B / m B) • m.inv.inv at hi
  simpa only [Measure.inv_inv] using hi

/-- A measure-preserving skew translation over a map of the section forces
that section map to preserve the marginal Haar factor. -/
theorem measurePreserving_base_of_left_skew (ν : Measure X) (m : Measure G)
    [SFinite ν] [SFinite m] [m.IsMulLeftInvariant]
    {T : X → X} (hT : Measurable T) {a : X → G} (ha : Measurable a)
    (hskew : MeasurePreserving (fun q : X × G => (T q.1, a q.1 * q.2))
      (ν.prod m) (ν.prod m))
    {B : Set G} (hB : MeasurableSet B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    MeasurePreserving T ν ν := by
  have hinv : MeasurePreserving (fun q : X × G => (q.1, (a q.1)⁻¹ * q.2))
      (ν.prod m) (ν.prod m) := by
    apply (MeasurePreserving.id ν).skew_product (g := fun x z => (a x)⁻¹ * z)
    · exact (ha.comp measurable_fst).inv.mul measurable_snd
    · exact Filter.Eventually.of_forall fun x => map_mul_left_eq_self m (a x)⁻¹
  have hbase : MeasurePreserving (fun q : X × G => (T q.1, q.2))
      (ν.prod m) (ν.prod m) := by
    simpa only [Function.comp_def, mul_inv_cancel_left] using hskew.comp hinv
  refine ⟨hT, ?_⟩
  ext E hE
  rw [Measure.map_apply hT hE]
  have he := hbase.measure_preimage (hE.prod hB).nullMeasurableSet
  change (ν.prod m) ((T ⁻¹' E) ×ˢ B) = (ν.prod m) (E ×ˢ B) at he
  simp only [Measure.prod_prod] at he
  exact (ENNReal.mul_left_inj hB0 hBtop).mp he

variable [TopologicalSpace G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  [TopologicalSpace X] [CompactSpace X]
  [IsFiniteMeasureOnCompacts M]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G]
  [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem haarFiberSlice_finiteOnCompacts {E : Set X} (hE : MeasurableSet E) :
    IsFiniteMeasureOnCompacts (haarFiberSlice M E) := ⟨by
    intro B hB
    rw [haarFiberSlice_apply M hE hB.measurableSet]
    exact (measure_mono (prod_mono (subset_univ E) Subset.rfl)).trans_lt
      (isCompact_univ.prod hB).measure_lt_top⟩

/-- Translation invariance forces all measurable rectangles to have the
product measure predicted by a single Haar normalization. -/
theorem haarProduct_rectangle (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {B : Set G} (hB : MeasurableSet B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞)
    {E : Set X} (hE : MeasurableSet E) {C : Set G} (hC : MeasurableSet C) :
    M (E ×ˢ C) = haarSectionMeasure M m B E * m C := by
  let := haarFiberSlice_rightInvariant M hM hE
  let := haarFiberSlice_finiteOnCompacts M hE
  have h := rightInvariant_eq_div_smul (haarFiberSlice M E) m hB0 hBtop
  have hc := congrArg (fun ρ : Measure G => ρ C) h
  simpa only [haarFiberSlice_apply M hE hC, Measure.smul_apply, smul_eq_mul,
    haarFiberSlice_apply M hE hB, haarSectionMeasure_apply M m hB hE] using hc

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G]
  [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The section measure has finite mass if the averaging region is compact. -/
theorem haarSectionMeasure_finite (m : Measure G) {B : Set G}
    (hB : IsCompact B) (hB0 : m B ≠ 0) :
    IsFiniteMeasure (haarSectionMeasure M m B) := by
  constructor
  rw [haarSectionMeasure_apply M m hB.measurableSet MeasurableSet.univ]
  exact ENNReal.div_lt_top (isCompact_univ.prod hB).measure_ne_top hB0

/-- Haar uniqueness on each section slice yields equality on the whole
product sigma algebra. -/
theorem haarProduct_factorization (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    M = (haarSectionMeasure M m B).prod m := by
  let := haarSectionMeasure_finite M m hB hB0
  symm
  apply Measure.prod_eq
  intro E C hE hC
  exact haarProduct_rectangle M m hM hB.measurableSet hB0 hBtop hE hC

/-- A nonzero invariant coupling has a finite nonzero section measure. -/
theorem haarSectionMeasure_ne_zero (m : Measure G) [SigmaFinite m] [m.IsMulRightInvariant]
    (hM : ∀ g : G, MeasurePreserving (fun q : X × G => (q.1, q.2 * g)) M M)
    (hM0 : M ≠ 0) {B : Set G} (hB : IsCompact B)
    (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    haarSectionMeasure M m B ≠ 0 := by
  intro hν
  apply hM0
  rw [haarProduct_factorization M m hM hB hB0 hBtop, hν, Measure.zero_prod]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The invariant measure on the inverse section

For the actual compact space of quasi-inverse pairs, the Haar coupling in
inverse coordinates factors as a finite nonzero invariant section measure
times Haar measure. No absolute continuity of the section measure is used.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- The product measure remains nonzero under the change of charts. -/
theorem inversePairCoupling_ne_zero
    (m : Measure G) [SFinite m] (hm : m ≠ 0)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ] :
    inversePairCoupling m μ ≠ 0 := by
  apply (Measure.map_ne_zero_iff pairChartTransition.continuous.measurable.aemeasurable).mpr
  intro h
  apply hm
  apply Measure.measure_univ_eq_zero.mp
  have hu := congrArg (fun ρ : Measure (G × NormalizedPair G Λ) => ρ univ) h
  simpa only [← univ_prod_univ, Measure.prod_prod, measure_univ, mul_one,
    Measure.coe_zero, Pi.zero_apply] using hu

/-- The inverse section has a finite nonzero stationary measure, and its
product with Haar measure is exactly the coupling in inverse coordinates. -/
theorem exists_inverseSection_measure
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] :
    ∃ ν : Measure (NormalizedPair G Λ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      inversePairCoupling m μ = ν.prod m := by
  obtain ⟨B, hB, hB0⟩ := (Measure.Regular.exists_isCompact_not_null (μ := m)).mpr (NeZero.ne m)
  let M := inversePairCoupling m μ
  let ν := haarSectionMeasure M m B
  have hright := measurePreserving_inversePairCoupling_right m μ
  have hfinite : IsFiniteMeasure ν := haarSectionMeasure_finite M m hB hB0
  let := hfinite
  have hprod : M = ν.prod m := haarProduct_factorization M m hright hB hB0 hB.measure_ne_top
  have hnonzero : ν ≠ 0 := haarSectionMeasure_ne_zero M m hright
    (inversePairCoupling_ne_zero m (NeZero.ne m) μ) hB hB0 hB.measure_ne_top
  refine ⟨ν, hfinite, hnonzero, ?_, hprod⟩
  constructor
  intro g E hE
  have ht := measurePreserving_inversePairCoupling_target m μ g⁻¹
  change MeasurePreserving (pairInverseTargetTranslation g⁻¹) M M at ht
  rw [hprod] at ht
  have hc : Continuous (normalizedTranslate (Λ := Λ) g⁻¹) := by
    have h : Continuous (fun p : NormalizedPair G Λ => g • p) := continuous_const_smul g
    exact h
  have hbase := measurePreserving_base_of_left_skew ν m hc.measurable
    (((continuous_eval_const g⁻¹).comp continuous_subtype_val.fst).inv.measurable)
    ht hB.measurableSet hB0 hB.measure_ne_top
  have hsmul : MeasurePreserving (fun p : NormalizedPair G Λ => g • p) ν ν := hbase
  exact hsmul.measure_preimage hE.nullMeasurableSet

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationarySlope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging the stationary height cocycle

The normalized pair space carries a measure-preserving action. Its height
evaluation is a cocycle for inverse pullback. We construct that action on the
actual space `L²`, and show that integration gives an additive slope. No
reduced-cohomology assertion is assumed in this construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G X W : Type} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X]
  [NormedAddCommGroup W]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

/-- Constants are invariant for a finite invariant measure, without a
probability normalization. -/
theorem stationaryPullback_const_finite [IsFiniteMeasure μ] (g : G) (w : W) :
    stationaryPullback μ g (Lp.const 2 μ w) = Lp.const 2 μ w := by
  apply Lp.ext
  have h := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ w)
  exact (Lp.coeFn_compMeasurePreserving _ (measurePreserving_smul g⁻¹ μ)).trans
    (h.trans (Lp.coeFn_const 2 μ w).symm)

section ContinuousAction

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [BorelSpace X] [R1Space X]
  [ContinuousSMul G X] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

/-- Strong continuity follows from the actual continuous action on the
underlying measure space and density of simple functions in `L²`. -/
theorem continuous_stationaryPullback :
    Continuous (fun z : G × Lp W 2 μ => stationaryPullback μ z.1 z.2) := by
  let T : G × Lp W 2 μ → C(X, X) := fun z =>
    ⟨fun x => z.1⁻¹ • x, continuous_const_smul _⟩
  have hT : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.inv).smul continuous_snd
  exact continuous_snd.compMeasurePreservingLp hT
    (fun z => measurePreserving_smul z.1⁻¹ μ) (by norm_num)

end ContinuousAction

variable [NormedSpace ℝ W] [CompleteSpace W]

/-- Ergodicity of the action, rather than an assumption about its Hilbert
representation, identifies all invariant `L²` vectors with constants. -/
theorem stationary_fixed_eq_const
    {G X W : Type} [Group G] [MeasurableSpace X] [MulAction G X]
    [MeasurableConstSMul G X] [NormedAddCommGroup W] [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ] (v : Lp W 2 μ)
    (hfix : ∀ g : G, stationaryPullback μ g v = v) :
    ∃ c : W, v = Lp.const 2 μ c := by
  borelize W
  have hc : ∃ c : W, (v : X → W) =ᵐ[μ] Function.const X c := by
    apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
    intro U hU
    apply eventuallyConst_set.mp
    apply aeconst_of_forall_preimage_smul_ae_eq G
      ((Lp.aestronglyMeasurable v).aemeasurable.nullMeasurable hU)
    intro g
    have heq : Lp.compMeasurePreserving (fun x : X => g • x)
        (measurePreserving_smul g μ) v = v := by
      simpa only [stationaryPullback, inv_inv] using hfix g⁻¹
    have hae := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g μ)
    rw [heq] at hae
    filter_upwards [hae] with x hx
    apply propext
    change (v (g • x) ∈ U ↔ v x ∈ U)
    rw [hx]
    rfl
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, Lp.ext (hc.trans (Lp.coeFn_const 2 μ c).symm)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryCentered
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The zero-mean Hilbert representation and stationary sublinearity

The closed kernel of integration is invariant under inverse pullback.
Ergodicity removes its invariant vectors. This constructs the representation
to which the published reduced-cohomology input is applied; the conclusion
is the manuscript's averaged sublinear estimate for a fixed measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {G X W : Type} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

omit [NormedSpace ℝ W] [CompleteSpace W] in
/-- Constant functions are fixed by inverse pullback. -/
theorem stationaryPullback_const (g : G) (w : W) :
    stationaryPullback μ g (Lp.const 2 μ w) = Lp.const 2 μ w := by
  apply Lp.ext
  have h := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ w)
  exact (Lp.coeFn_compMeasurePreserving _ (measurePreserving_smul g⁻¹ μ)).trans
    (h.trans (Lp.coeFn_const 2 μ w).symm)

attribute [local instance] zeroMeanL2Action

/-- Ergodicity removes every invariant vector from the zero-mean subspace. -/
theorem zeroMeanL2_no_fixed
    {G X W : Type} [Group G] [MeasurableSpace X] [MulAction G X]
    [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    (v : ZeroMeanL2 (W := W) μ) (hfix : ∀ g : G, g • v = v) : v = 0 := by
  obtain ⟨w, hw⟩ := stationary_fixed_eq_const μ (v : Lp W 2 μ)
    (fun g => congrArg Subtype.val (hfix g))
  have hmean : stationaryL2Mean μ (v : Lp W 2 μ) = 0 := v.property
  rw [hw, stationaryL2Mean_const] at hmean
  apply Subtype.ext
  rw [hw, hmean, map_zero]
  rfl

theorem isCocycle_centeredL2 (b : G → Lp W 2 μ) (hb : IsCocycle b) :
    IsCocycle (centeredL2Cocycle μ b) := by
  intro g h
  apply Subtype.ext
  change b (g * h) - Lp.const 2 μ (stationaryL2Mean μ (b (g * h))) =
    (b g - Lp.const 2 μ (stationaryL2Mean μ (b g))) +
      stationaryPullback μ g (b h - Lp.const 2 μ (stationaryL2Mean μ (b h)))
  have hmean : stationaryL2Mean μ (g • b h) = stationaryL2Mean μ (b h) :=
    stationaryL2Mean_pullback μ g (b h)
  rw [hb g h, map_add, hmean, map_add,
    map_sub, stationaryPullback_const]
  rw [show g • b h = stationaryPullback μ g (b h) from rfl]
  abel

theorem continuous_centeredL2 {G : Type} [Group G] [TopologicalSpace G]
    (b : G → Lp W 2 μ) (hb : Continuous b) : Continuous (centeredL2Cocycle μ b) := by
  exact (hb.sub ((Lp.constL 2 μ ℝ).continuous.comp
    ((stationaryL2Mean μ).continuous.comp hb))).subtype_mk _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PairHeightCocycle
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Height evaluation on the compact pair space

The normalized action makes evaluation of a continuous height homomorphism
an actual continuous `L²` cocycle. The stationary slope estimate therefore
applies to this concrete cocycle.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Λ : ℝ≥0}

omit [IsIsometricSMul G G] [NormedSpace ℝ W] [IsTopologicalGroup G] in
theorem continuous_pairHeightProfile (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (pairHeightProfile (Λ := Λ) π hπ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_pairHeight π hπ

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]

omit [IsIsometricSMul G G] in
theorem continuous_pairHeightL2 (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (pairHeightL2 (Λ := Λ) μ π hπ) :=
  (ContinuousMap.toLp 2 μ ℝ).continuous.comp (continuous_pairHeightProfile π hπ)

attribute [local instance] stationaryL2Action
attribute [local instance] zeroMeanL2Action

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CouplingTransfer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer functions in the two coupling charts

The transfer is lifted by adding target height. Its domain defect is the
original stationary cocycle defect. In inverse coordinates, differences
inside a fiber are the same defects, and fiber averaging gives the exact
inverse transfer identity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [NormedAddCommGroup W]

omit [ProperSpace G] in
theorem pairTransferLift_domain (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (t : G) (q : G × NormalizedPair G Λ) :
    pairTransferLift π φ (pairDomainTranslation t q) - pairTransferLift π φ q -
      (l t).toAdd = pairTransferDefect π l φ t q.2 := by
  simp only [pairTransferLift, pairDomainTranslation, pairTransferDefect, pairHeight,
    map_mul π, toAdd_mul]
  abel

/-- The inverse chart intertwines domain translation with right translation
inside each fiber. -/
theorem pairChartTransition_symm_domain (t : G) (q : NormalizedPair G Λ × G) :
    pairDomainTranslation t (pairChartTransition.symm q) =
      pairChartTransition.symm (q.1, q.2 * t) := by
  apply pairChartTransition.injective
  rw [pairChartTransition_domain, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- Differences of two fiber values are original cocycle defects. -/
theorem inverseFiberTransfer_sub (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (p : NormalizedPair G Λ) (x₁ x₂ : G) :
    inverseFiberTransfer π l φ (p, x₁) - inverseFiberTransfer π l φ (p, x₂) =
      pairTransferDefect π l φ (x₂⁻¹ * x₁)
        (pairChartTransition.symm (p, x₂)).2 := by
  have h := pairTransferLift_domain π l φ (x₂⁻¹ * x₁)
    (pairChartTransition.symm (p, x₂))
  rw [pairChartTransition_symm_domain, mul_inv_cancel_left] at h
  simp only [inverseFiberTransfer, map_mul l, map_inv l, toAdd_mul, toAdd_inv] at *
  rw [← h]
  abel

/-- Target translation in the inverse chart, expressed back in target
coordinates. -/
theorem pairChartTransition_symm_target (y : G) (q : NormalizedPair G Λ × G) :
    pairChartTransition.symm (pairInverseTargetTranslation y q) =
      (y⁻¹ * (pairChartTransition.symm q).1, (pairChartTransition.symm q).2) := by
  apply pairChartTransition.injective
  rw [Homeomorph.apply_symm_apply, pairChartTransition_target,
    Homeomorph.apply_symm_apply]

/-- The pointwise target transfer identity before averaging. -/
theorem inverseFiberTransfer_target (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (q : NormalizedPair G Λ × G) :
    inverseFiberTransfer π l φ (pairInverseTargetTranslation y q) =
      inverseFiberTransfer π l φ q - (π y).toAdd + (l (q.1.val.1 y)).toAdd := by
  unfold inverseFiberTransfer
  rw [pairChartTransition_symm_target]
  simp only [pairTransferLift, pairInverseTargetTranslation,
    map_mul π, map_inv π, map_mul l, map_inv l, toAdd_mul, toAdd_inv]
  abel

/-- A version with a fixed integration coordinate, suitable for averaging. -/
theorem inverseFiberTransfer_normalizedTranslate (π l : G →* Multiplicative W)
    (φ : NormalizedPair G Λ → W) (y : G) (p : NormalizedPair G Λ) (x : G) :
    inverseFiberTransfer π l φ (normalizedTranslate y p, x) =
      inverseFiberTransfer π l φ (p, p.val.1 y * x) -
        (π y).toAdd + (l (p.val.1 y)).toAdd := by
  simpa only [pairInverseTargetTranslation, inv_mul_cancel_left] using
    inverseFiberTransfer_target π l φ y (p, p.val.1 y * x)

variable [MeasurableSpace G] [NormedSpace ℝ W] [CompleteSpace W]

/-- Averaging yields the exact inverse-transfer identity; integrability is
required only on the two regions actually being averaged. -/
theorem inverseAveragedTransfer_identity (β : Measure G) [IsProbabilityMeasure β]
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (y : G) (p : NormalizedPair G Λ)
    (h₁ : Integrable (fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x)) β)
    (h₂ : Integrable (fun x => inverseFiberTransfer π l φ (p, x)) β) :
    inverseAveragedTransfer β π l φ (normalizedTranslate y p) -
      inverseAveragedTransfer β π l φ p =
      -(π y).toAdd + (l (p.val.1 y)).toAdd + inverseAverageError β π l φ y p := by
  unfold inverseAveragedTransfer inverseAverageError
  simp_rw [inverseFiberTransfer_normalizedTranslate]
  rw [integral_add (f := fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x) - (π y).toAdd) (h₁.sub (integrable_const ((π y).toAdd)))
      (integrable_const ((l (p.val.1 y)).toAdd)),
    integral_sub (f := fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x)) h₁ (integrable_const ((π y).toAdd)), integral_const, integral_const,
    integral_sub h₁ h₂]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CouplingLocalL2
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local square integrability of the coupling transfers

A square-integrable section transfer becomes locally square integrable after
adding the continuous target height. This property is preserved by the
actual change to inverse coordinates.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [SecondCountableTopology W]

omit [IsIsometricSMul G G] in
/-- The lifted transfer is square integrable on every compact subset of the
first product chart. -/
theorem pairTransferLift_memLp_compact
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {K : Set (G × NormalizedPair G Λ)} (hK : IsCompact K) :
    MemLp (pairTransferLift π φ) 2 ((m.prod μ).restrict K) := by
  have hc : Continuous (fun q : G × NormalizedPair G Λ => (π q.1).toAdd) :=
    hπ.comp continuous_fst
  have hh : MemLp (fun q : G × NormalizedPair G Λ => (π q.1).toAdd) 2
      ((m.prod μ).restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ContinuousOn.integrableOn_compact hK (hc.norm.pow 2).continuousOn
  have hC : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  let : IsFiniteMeasure (m.restrict (Prod.fst '' K)) :=
    isFiniteMeasure_restrict.mpr hC.measure_ne_top
  have hs := hφ.comp_snd (m.restrict (Prod.fst '' K))
  rw [Measure.restrict_prod_eq_prod_univ] at hs
  have hsub : K ⊆ (Prod.fst '' K) ×ˢ univ := by
    intro q hq
    exact ⟨⟨q, hq, rfl⟩, mem_univ _⟩
  exact hh.add (hs.mono_measure (Measure.restrict_mono_set _ hsub))

/-- The corrected transfer in the inverse chart is locally square
integrable for the coupling measure. -/
theorem inverseFiberTransfer_memLp_compact
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {K : Set (NormalizedPair G Λ × G)} (hK : IsCompact K) :
    MemLp (inverseFiberTransfer π l φ) 2 ((inversePairCoupling m μ).restrict K) := by
  let e : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) := pairChartTransition
  have he : MeasurePreserving e.symm (inversePairCoupling m μ) (m.prod μ) :=
    MeasurableEquiv.measurePreserving_symm (m.prod μ) e.toMeasurableEquiv
  have hr := he.restrict_image_emb e.symm.measurableEmbedding K
  have hLift := (pairTransferLift_memLp_compact m μ π hπ hφ
    (hK.image e.symm.continuous)).comp_measurePreserving hr
  have hc : Continuous (fun q : NormalizedPair G Λ × G => (l q.2).toAdd) :=
    hl.comp continuous_snd
  have hh : MemLp (fun q : NormalizedPair G Λ × G => (l q.2).toAdd) 2
      ((inversePairCoupling m μ).restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ContinuousOn.integrableOn_compact hK (hc.norm.pow 2).continuousOn
  exact hLift.sub hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiberAverageL2
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-integrable averages over probability fibers

These estimates justify the whole-fiber averages in the inverse coupling.
The outer measure may be finite without being normalized.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PolycyclicRecognition

variable {X Y W : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A positive finite region defines a probability measure on its whole
volume, rather than on a chosen representative point. -/
theorem normalizedRestriction_probability (m : Measure Y) {B : Set Y}
    (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    IsProbabilityMeasure (normalizedRestriction m B) := by
  constructor
  rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hB0 hBtop]

omit [NormedSpace ℝ W] in
/-- Normalizing one finite fiber preserves square integrability. -/
theorem memLp_normalizedRestriction_product (ν : Measure X) [SFinite ν]
    (m : Measure Y) [SFinite m] {B : Set Y} (hB0 : m B ≠ 0)
    {f : X × Y → W} (hf : MemLp f 2 (ν.prod (m.restrict B))) :
    MemLp f 2 (ν.prod (normalizedRestriction m B)) := by
  rw [normalizedRestriction, Measure.prod_smul_right]
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr hB0)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Normalizing both averaging variables contributes exactly the inverse
square of the region's mass. -/
theorem lintegral_normalizedRestriction_two (ν : Measure X) (m : Measure Y)
    {B : Set Y} (hB0 : m B ≠ 0) (f : X → Y → Y → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, f x y z ∂(normalizedRestriction m B)
      ∂(normalizedRestriction m B) ∂ν) =
      ((m B)⁻¹) ^ 2 * ∫⁻ x, ∫⁻ y in B, ∫⁻ z in B, f x y z ∂m ∂m ∂ν := by
  simp_rw [normalizedRestriction, lintegral_smul_measure, smul_eq_mul,
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hB0)]
  rw [pow_two]
  ac_rfl

/-- Jensen's square estimate for the norm of a Bochner average. -/
theorem norm_integral_sq_le (β : Measure Y) [IsProbabilityMeasure β]
    {f : Y → W} (hf : MemLp f 2 β) :
    ‖∫ y, f y ∂β‖ ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂β := by
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun y => norm_nonneg (f y)) hfi.norm hsq
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 2).trans hj

/-- The nonnegative extended-real form of the square estimate, used with
Tonelli when comparing whole fibers. -/
theorem enorm_integral_sq_le (β : Measure Y) [IsProbabilityMeasure β]
    {f : Y → W} (hf : MemLp f 2 β) :
    ‖∫ y, f y ∂β‖ₑ ^ 2 ≤ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂β := by
  have h := ENNReal.ofReal_le_ofReal (norm_integral_sq_le β hf)
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [ofReal_integral_eq_lintegral_ofReal hsq
    (Filter.Eventually.of_forall fun y => sq_nonneg ‖f y‖)] at h
  simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using h

/-- A square-integrable function on a finite product has square-integrable
fiber averages, with the expected contraction of the squared norm. -/
theorem memLp_fiberAverage (ν : Measure X) [IsFiniteMeasure ν]
    (β : Measure Y) [IsProbabilityMeasure β]
    {f : X × Y → W} (hf : MemLp f 2 (ν.prod β)) :
    MemLp (fun x => ∫ y, f (x, y) ∂β) 2 ν ∧
      (∫ x, ‖∫ y, f (x, y) ∂β‖ ^ 2 ∂ν) ≤
        ∫ q, ‖f q‖ ^ 2 ∂(ν.prod β) := by
  have hmeas := hf.aestronglyMeasurable.integral_prod_right'
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hsect : ∀ᵐ x ∂ν, MemLp (fun y => f (x, y)) 2 β := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      (integrable_prod_iff hsq.aestronglyMeasurable).mp hsq |>.1] with x hx hix
    exact (memLp_two_iff_integrable_sq_norm hx).mpr hix
  have hbound : ∀ᵐ x ∂ν,
      ‖∫ y, f (x, y) ∂β‖ ^ 2 ≤ ∫ y, ‖f (x, y)‖ ^ 2 ∂β :=
    hsect.mono fun _ hx => norm_integral_sq_le β hx
  have hint : Integrable (fun x => ‖∫ y, f (x, y) ∂β‖ ^ 2) ν := by
    apply hsq.integral_prod_left.mono'
      (hmeas.norm.pow 2)
    filter_upwards [hbound] with x hx
    change |‖∫ y, f (x, y) ∂β‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hx
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).mpr hint, ?_⟩
  rw [integral_prod _ hsq]
  exact integral_mono_ae hint hsq.integral_prod_left hbound

/-- Extended-real version of the whole-product oscillation estimate. -/
theorem enorm_sub_integral_sq_le [CompleteSpace W]
    (β : Measure Y) [IsProbabilityMeasure β]
    {f g : Y → W} (hf : MemLp f 2 β) (hg : MemLp g 2 β) :
    ‖(∫ y, f y ∂β) - ∫ y, g y ∂β‖ₑ ^ 2 ≤
      ∫⁻ y, ∫⁻ z, ‖f y - g z‖ₑ ^ 2 ∂β ∂β := by
  have hfg : MemLp (fun q : Y × Y => f q.1 - g q.2) 2 (β.prod β) :=
    (hf.comp_fst β).sub (hg.comp_snd β)
  have hi := enorm_integral_sq_le (β.prod β) hfg
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgi := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [integral_prod _ (hfg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))] at hi
  have hev : (∫ y, ∫ z, f y - g z ∂β ∂β) = (∫ y, f y ∂β) - ∫ z, g z ∂β := by
    have hin (y : Y) : (∫ z, f y - g z ∂β) = f y - ∫ z, g z ∂β := by
      rw [integral_sub (integrable_const (f y)) hgi, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp_rw [hin]
    rw [integral_sub hfi (integrable_const (∫ z, g z ∂β)), integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hev, lintegral_prod _ (hfg.aestronglyMeasurable.enorm.pow_const 2)] at hi
  exact hi

/-- The integrated error of fiber averages is controlled by the integrated
oscillation over the full product of the fibers. -/
theorem fiber_average_error_lintegral_le [CompleteSpace W]
    (ν : Measure X) [IsFiniteMeasure ν] (β : Measure Y) [IsProbabilityMeasure β]
    {f g : X × Y → W} (hf : MemLp f 2 (ν.prod β)) (hg : MemLp g 2 (ν.prod β)) :
    (∫⁻ x, ‖∫ y, f (x, y) - g (x, y) ∂β‖ₑ ^ 2 ∂ν) ≤
      ∫⁻ x, ∫⁻ y, ∫⁻ z, ‖f (x, y) - g (x, z)‖ₑ ^ 2 ∂β ∂β ∂ν := by
  have hfsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  apply lintegral_mono_ae
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hg.aestronglyMeasurable.prodMk_left,
    (integrable_prod_iff hfsq.aestronglyMeasurable).mp hfsq |>.1,
    (integrable_prod_iff hgsq.aestronglyMeasurable).mp hgsq |>.1] with x hfm hgm hfi hgi
  have hfx := (memLp_two_iff_integrable_sq_norm hfm).mpr hfi
  have hgx := (memLp_two_iff_integrable_sq_norm hgm).mpr hgi
  rw [integral_sub (hfx.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (hgx.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  exact enorm_sub_integral_sq_le β hfx hgx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiberIncrementBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing whole fibers by bounded increments

Tonelli and the left-Haar change of variables turn a two-region oscillation
integral into a bounded-parameter integral of the original increment errors.
The translating center may depend on the section point.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PolycyclicRecognition

variable {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableInv G] [MeasurableSpace X]

omit [MeasurableInv G] in
/-- Enlarge a translated averaging region using its actual inclusion.
The integrand needs no regularity for this step. -/
theorem lintegral_translate_le (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (q : G) {B C : Set G} (h : ∀ x ∈ B, q * x ∈ C) :
    (∫⁻ x in B, f (q * x) ∂m) ≤ ∫⁻ x in C, f x ∂m := by
  rw [(measurePreserving_mul_left m q).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft q).measurableEmbedding f B]
  exact lintegral_mono_set (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- The substitution `t = x₂⁻¹x₁` bounds whole-region oscillations by
increments whose parameters lie in one fixed set. -/
theorem fiber_increment_lintegral_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun q : X × G × G => f q.1 q.2.1 q.2.2)) :
    (∫⁻ p, ∫⁻ x₁ in C, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * x₁) ∂m ∂m ∂ν) ≤
      ∫⁻ t in T, ∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν ∂m := by
  have hp (p : X) : Measurable (fun q : G × G => f p q.1 q.2) :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  calc
    _ = ∫⁻ p, ∫⁻ x₂ in B, ∫⁻ x₁ in C, f p x₂ (x₂⁻¹ * x₁) ∂m ∂m ∂ν := by
      apply lintegral_congr
      intro p
      exact lintegral_lintegral_swap ((hp p).comp
        (measurable_snd.prodMk (measurable_snd.inv.mul measurable_fst))).aemeasurable
    _ ≤ ∫⁻ p, ∫⁻ x₂ in B, ∫⁻ t in T, f p x₂ t ∂m ∂m ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with x₂ hx₂
      have heq : (∫⁻ x₁ in C, f p x₂ (x₂⁻¹ * x₁) ∂m) =
          ∫⁻ t in (fun t => x₂ * t) ⁻¹' C, f p x₂ t ∂m := by
        have h := (measurePreserving_mul_left m x₂).setLIntegral_comp_preimage_emb
          (MeasurableEquiv.mulLeft x₂).measurableEmbedding
          (fun x₁ => f p x₂ (x₂⁻¹ * x₁)) C
        simpa only [inv_mul_cancel_left] using h.symm
      rw [heq]
      apply lintegral_mono_set
      intro t ht
      have h := hT x₂ hx₂ (x₂ * t) ht
      simpa only [inv_mul_cancel_left] using h
    _ = ∫⁻ p, ∫⁻ t in T, ∫⁻ x₂ in B, f p x₂ t ∂m ∂m ∂ν := by
      apply lintegral_congr
      intro p
      exact lintegral_lintegral_swap (hp p).aemeasurable
    _ = _ := by
      apply lintegral_lintegral_swap
      have hm : Measurable (fun q : (X × G) × G => f q.1.1 q.2 q.1.2) :=
        hf.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
      exact (hm.lintegral_prod_right' (ν := m.restrict B)).aemeasurable

/-- The two-region estimate remains uniform when the first averaging
region is translated by a center depending on the section point. -/
theorem fiber_translated_increment_lintegral_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (q : X → G) (hC : ∀ p x, x ∈ B → q p * x ∈ C)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun a : X × G × G => f a.1 a.2.1 a.2.2)) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * (q p * x₁)) ∂m ∂m ∂ν) ≤
      ∫⁻ t in T, ∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν ∂m := by
  refine le_trans (lintegral_mono fun p => ?_)
    (fiber_increment_lintegral_le ν m hB hT f hf)
  exact lintegral_translate_le m
    (fun x₁ => ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * x₁) ∂m) (q p) (hC p)

/-- Uniform control on the compact increment region bounds the whole
oscillation integral by the Haar mass of that region. -/
theorem fiber_translated_increment_uniform_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (q : X → G) (hC : ∀ p x, x ∈ B → q p * x ∈ C)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun a : X × G × G => f a.1 a.2.1 a.2.2))
    {c : ℝ≥0∞} (hbound : ∀ t ∈ T, (∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν) ≤ c) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * (q p * x₁)) ∂m ∂m ∂ν) ≤
      c * m T := by
  refine (fiber_translated_increment_lintegral_le ν m hB hT q hC f hf).trans ?_
  calc
    _ ≤ ∫⁻ _t in T, c ∂m := lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hTm] with t ht using hbound t ht)
    _ = _ := by rw [setLIntegral_const]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeodesicWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word decompositions by sampling minimizing paths

This supplies the bounded-step word decomposition used in the stationary
estimate from actual metric paths. The number of steps is at most distance
plus one.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- Subdivision of a minimizing path gives a word in the unit ball, with
length at most distance plus one. -/
theorem wordFactorization_of_minimizing_paths
    {G : Type} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (g : G) :
    ∃ w : List G, (∀ q ∈ w, q ∈ closedBall 1 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ dist 1 g + 1 := by
  obtain ⟨γ, h0, h1, hγ⟩ := hpath g
  let n := ⌊dist 1 g⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : dist 1 g ≤ (n : ℝ) := by
    simpa [n] using (Nat.lt_floor_add_one (dist 1 g)).le
  let v : ℕ → G := fun k => γ ((k : ℝ) / n)
  let w := (List.range n).map (fun k => (v k)⁻¹ * v (k + 1))
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have hk' : k < n := List.mem_range.mp hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk'.le
    have hks : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk'
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hkn⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hks⟩
    have hdiff : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    have hd : dist 1 ((v k)⁻¹ * v (k + 1)) = dist (v k) (v (k + 1)) := by
      simpa using (dist_mul_left (v k) (1 : G) ((v k)⁻¹ * v (k + 1))).symm
    rw [mem_closedBall, dist_comm, hd]
    refine (hγ _ ht _ hu).trans ?_
    rw [hdiff, mul_one_div]
    exact (div_le_one hnr).mpr hlen
  · have hp := List.prod_range_div' n (fun k => (v k)⁻¹)
    have hv0 : v 0 = 1 := by simp [v, h0]
    have hvn : v n = g := by simp [v, h1, hnr.ne']
    simpa [w, div_eq_mul_inv, hv0, hvn] using hp
  · simpa [w, n, Nat.cast_add, Nat.cast_one] using
      add_le_add_right (Nat.floor_le (dist_nonneg (x := (1 : G)) (y := g))) 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseAverageL2
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse transfer belongs to L²

The transfer in inverse coordinates is averaged over an actual positive
compact Haar region. Local L² integrability and Jensen's estimate justify
this construction for the finite inverse-section measure.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]

omit [CompleteSpace W] [NormedSpace ℝ W] in
/-- The corrected inverse transfer is square integrable on a normalized
compact fiber region. -/
theorem inverseFiberTransfer_memLp_normalized
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseFiberTransfer π l φ) 2 (ν.prod (normalizedRestriction m B)) := by
  have hf := inverseFiberTransfer_memLp_compact m μ π l hπ hl hφ
    (isCompact_univ.prod hB)
  rw [hprod, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  exact memLp_normalizedRestriction_product ν m hB0 hf

omit [CompleteSpace W] in
/-- Translating the compact fiber region by its evaluation center retains
square integrability. Stationarity handles the normalized section shift. -/
theorem inverseFiberTransfer_shift_memLp
    (ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (β : Measure G) [IsProbabilityMeasure β]
    (π l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    (φ : NormalizedPair G Λ → W)
    (hD : MemLp (inverseFiberTransfer π l φ) 2 (ν.prod β)) (y : G) :
    MemLp (fun q : NormalizedPair G Λ × G =>
      inverseFiberTransfer π l φ (q.1, q.1.val.1 y * q.2)) 2 (ν.prod β) := by
  have hT : MeasurePreserving (normalizedTranslate (Λ := Λ) y) ν ν := by
    have h := measurePreserving_smul y⁻¹ ν
    change MeasurePreserving (fun p => normalizedTranslate (y⁻¹)⁻¹ p) ν ν at h
    simpa only [inv_inv] using h
  have hshift := hD.comp_measurePreserving (hT.prod (MeasurePreserving.id β))
  let c : C(NormalizedPair G Λ, W) :=
    ⟨fun p => (π y).toAdd - (l (p.val.1 y)).toAdd,
      continuous_const.sub (hl.comp ((continuous_eval_const y).comp continuous_subtype_val.fst))⟩
  have hc : MemLp (fun p : NormalizedPair G Λ => (π y).toAdd - (l (p.val.1 y)).toAdd) 2 ν :=
    ContinuousMap.memLp (μ := ν) (p := 2) ℝ c
  have hs : MemLp (fun q : NormalizedPair G Λ × G =>
      inverseFiberTransfer π l φ (normalizedTranslate y q.1, q.2) +
        ((π y).toAdd - (l (q.1.val.1 y)).toAdd)) 2 (ν.prod β) :=
    hshift.add (hc.comp_fst β)
  apply (memLp_congr_ae ?_).mp hs
  filter_upwards with q
  have h := inverseFiberTransfer_normalizedTranslate π l φ y q.1 q.2
  change inverseFiberTransfer π l φ (normalizedTranslate y q.1, q.2) +
      ((π y).toAdd - (l (q.1.val.1 y)).toAdd) = _
  rw [h]
  abel

omit [CompleteSpace W] in
/-- The averaged inverse transfer is an actual square-integrable function
for the section measure constructed by Haar factorization. -/
theorem inverseAveragedTransfer_memLp
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseAveragedTransfer (normalizedRestriction m B) π l φ) 2 ν := by
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  exact (memLp_fiberAverage ν (normalizedRestriction m B)
    (inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0)).1

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Algebraic final step of the inverse transfer: the linear coefficient is
precisely the inverse of the original coefficient. -/
theorem inverse_transfer_linear_coefficient (A : W ≃L[ℝ] W)
    {v w ψ ψ' R : W} (h : ψ' - ψ = -v + A w + R) :
    w + (-A.symm ψ') - (-A.symm ψ) = A.symm v - A.symm R := by
  have ha := congrArg A.symm h
  simp only [map_sub, map_neg, map_add, ContinuousLinearEquiv.symm_apply_apply] at ha
  have heq : A.symm ψ' - A.symm ψ = -A.symm v + w + A.symm R := ha
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InverseCompactControl
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact regions in the inverse coupling

A compact family of evaluation points yields common compact averaging and
increment regions. Integrals on an inverse-chart strip are bounded by a
fixed Haar mass times the original section integral.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace PolycyclicRecognition

variable {G : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

omit [IsIsometricSMul G G] in
/-- Uniform compact regions for the centers, their translated averaging
regions, and the resulting difference parameters. -/
theorem exists_inverse_compact_regions {Q B : Set G} (hQ : IsCompact Q) (hB : IsCompact B) :
    ∃ C T : Set G, IsCompact C ∧ IsCompact T ∧
      (∀ y ∈ Q, ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C) ∧
      (∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T) := by
  let Q₁ : Set G := (fun q : NormalizedPair G Λ × G => q.1.val.1 q.2) '' (univ ×ˢ Q)
  have hQ₁ : IsCompact Q₁ := (isCompact_univ.prod hQ).image (by fun_prop)
  refine ⟨Q₁ * B, B⁻¹ * (Q₁ * B), hQ₁.mul hB, hB.inv.mul (hQ₁.mul hB), ?_, ?_⟩
  · intro y hy p x hx
    apply Set.mul_mem_mul
    · exact ⟨(p, y), ⟨mem_univ p, hy⟩, rfl⟩
    · exact hx
  · intro x₂ hx₂ x₁ hx₁
    exact Set.mul_mem_mul (Set.inv_mem_inv.mpr hx₂) hx₁

theorem inverseStripBase_compact {B : Set G} (hB : IsCompact B) :
    IsCompact (inverseStripBase (Λ := Λ) B) :=
  (((isCompact_univ.prod hB).image pairChartTransition.symm.continuous).image continuous_fst)

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Product coordinates bound every inverse-strip integral by the Haar mass
of one compact base projection times its section integral. -/
theorem inverse_strip_lintegral_le
    (m : Measure G) [SFinite m]
    (μ ν : Measure (NormalizedPair G Λ)) [SFinite μ] [SFinite ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (B : Set G) (f : NormalizedPair G Λ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, ∫⁻ x in B, f (pairChartTransition.symm (p, x)).2 ∂m ∂ν) ≤
      m (inverseStripBase (Λ := Λ) B) * ∫⁻ p, f p ∂μ := by
  let e : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) := pairChartTransition
  have he : MeasurePreserving e.symm (ν.prod m) (m.prod μ) := by
    rw [← hprod]
    exact MeasurableEquiv.measurePreserving_symm (m.prod μ) e.toMeasurableEquiv
  have hmeas : Measurable (fun q : NormalizedPair G Λ × G => f (e.symm q).2) :=
    hf.comp (measurable_snd.comp e.symm.continuous.measurable)
  calc
    _ = ∫⁻ q in (univ ×ˢ B : Set (NormalizedPair G Λ × G)), f (e.symm q).2 ∂(ν.prod m) := by
      rw [setLIntegral_prod _ hmeas.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ q in e.symm '' (univ ×ˢ B : Set (NormalizedPair G Λ × G)), f q.2 ∂(m.prod μ) :=
      he.setLIntegral_comp_emb e.symm.measurableEmbedding (fun q => f q.2) _
    _ ≤ ∫⁻ q in (inverseStripBase (Λ := Λ) B) ×ˢ univ, f q.2 ∂(m.prod μ) := by
      apply lintegral_mono_set
      intro q hq
      exact ⟨⟨q, hq, rfl⟩, mem_univ _⟩
    _ = _ := by
      rw [setLIntegral_prod (fun q : G × NormalizedPair G Λ => f q.2) (hf.comp measurable_snd).aemeasurable,
        Measure.restrict_univ]
      dsimp only [Prod.snd]
      rw [setLIntegral_const, mul_comm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseDefectControl
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlling inverse oscillations by the original defects

This is the compact-region estimate in the inverse-coupling argument. All
three integrations are over whole fibers. Their bound is a fixed product
of Haar masses times the original section error.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]

/-- Joint measurability of the actual stationary coboundary defect. -/
theorem measurable_pairTransferDefect (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : Measurable φ) :
    Measurable (fun q : G × NormalizedPair G Λ => pairTransferDefect π l φ q.1 q.2) := by
  have hT : Continuous (fun q : G × NormalizedPair G Λ => normalizedTranslate q.1 q.2) := by
    apply Continuous.subtype_mk
    exact continuous_translatePair.comp (continuous_fst.prodMk continuous_snd.subtype_val)
  have hb : Continuous (fun q : G × NormalizedPair G Λ => pairHeight π q.1 q.2) := by
    unfold pairHeight
    exact hπ.comp (by fun_prop)
  exact ((hb.measurable.add (hφ.comp hT.measurable)).sub
    (hφ.comp measurable_snd)).sub (hl.measurable.comp measurable_fst)

/-- The inverse oscillation integral over bounded regions is bounded by the
original section defect, with constants independent of the translating
center. -/
theorem inverse_defect_oscillation_bound
    (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    (μ ν : Measure (NormalizedPair G Λ)) [SFinite μ] [SFinite ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : Measurable φ)
    {B C T : Set G} (hB : MeasurableSet B) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (y : G) (hC : ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℝ≥0∞}
    (hc : ∀ t ∈ T, (∫⁻ p, ‖pairTransferDefect π l φ t p‖ₑ ^ 2 ∂μ) ≤ c) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B,
      ‖pairTransferDefect π l φ (x₂⁻¹ * (p.val.1 y * x₁))
        (pairChartTransition.symm (p, x₂)).2‖ₑ ^ 2 ∂m ∂m ∂ν) ≤
      (m (inverseStripBase (Λ := Λ) B) * c) * m T := by
  let f := fun (p : NormalizedPair G Λ) (x t : G) =>
    ‖pairTransferDefect π l φ t (pairChartTransition.symm (p, x)).2‖ₑ ^ 2
  have hd := measurable_pairTransferDefect π l hπ hl hφ
  have hf : Measurable (fun q : NormalizedPair G Λ × G × G => f q.1 q.2.1 q.2.2) := by
    have hm : Measurable (fun q : NormalizedPair G Λ × G × G =>
        (q.2.2, (pairChartTransition.symm (q.1, q.2.1)).2)) :=
      measurable_snd.snd.prodMk ((pairChartTransition.symm.continuous.measurable.comp
        (measurable_fst.prodMk measurable_snd.fst)).snd)
    exact (hd.comp hm).enorm.pow_const 2
  apply fiber_translated_increment_uniform_le ν m hB hTm hT
    (fun p : NormalizedPair G Λ => p.val.1 y) hC f hf
  intro t ht
  have htmeas : Measurable (fun p : NormalizedPair G Λ => ‖pairTransferDefect π l φ t p‖ₑ ^ 2) :=
    (hd.comp (measurable_const.prodMk measurable_id)).enorm.pow_const 2
  exact (inverse_strip_lintegral_le m μ ν hprod B _ htmeas).trans
    (mul_le_mul_right (hc t ht) _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseErrorBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized inverse-transfer error bound

The actual error of the averaged inverse transfer is controlled by the
original stationary defect on one compact increment region. Every factor
in the bound is independent of the chosen evaluation point in that region.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
  [MeasurableSpace W] [BorelSpace W]

/-- Quantitative whole-fiber estimate for the actual averaged inverse error.
The original defect bound is used only on the displayed increment set. -/
theorem inverseAverageError_lintegral_le
    (m : Measure G) [m.IsHaarMeasure]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ) (hφm : Measurable φ)
    {B C T : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (y : G) (hC : ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℝ≥0∞}
    (hc : ∀ t ∈ T, (∫⁻ p, ‖pairTransferDefect π l φ t p‖ₑ ^ 2 ∂μ) ≤ c) :
    (∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν) ≤
      ((m B)⁻¹) ^ 2 * ((m (inverseStripBase (Λ := Λ) B) * c) * m T) := by
  let β := normalizedRestriction m B
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  have hD := inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0
  have hS := inverseFiberTransfer_shift_memLp ν β π l hl φ hD y
  have hAvg := fiber_average_error_lintegral_le ν β hS hD
  change (∫⁻ p, ‖inverseAverageError β π l φ y p‖ₑ ^ 2 ∂ν) ≤ _ at hAvg
  simp_rw [inverseFiberTransfer_sub] at hAvg
  rw [lintegral_normalizedRestriction_two ν m hB0] at hAvg
  refine hAvg.trans ?_
  exact mul_le_mul_right (inverse_defect_oscillation_bound m μ ν hprod π l hπ hl hφm
    hB.measurableSet hTm hT y hC hc) _

/-- Compact-uniform vanishing of the original defects implies uniform
vanishing of the squared inverse-average errors on the chosen region. -/
theorem inverseAverageError_tendsto_uniform
    (m : Measure G) [m.IsHaarMeasure]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W)
    (hφ : ∀ n, MemLp (φ n) 2 μ) (hφm : ∀ n, Measurable (φ n))
    {B C T Q : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hTc : IsCompact T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (hC : ∀ y ∈ Q, ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℕ → ℝ≥0∞} (hc : Filter.Tendsto c Filter.atTop (nhds 0))
    (hbound : ∀ n t, t ∈ T → (∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) ≤ c n) :
    Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0) := by
  let K : ℝ≥0∞ := ((m B)⁻¹) ^ 2 * m (inverseStripBase (Λ := Λ) B) * m T
  have hK : K ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hB0))
      (inverseStripBase_compact hB).measure_ne_top) hTc.measure_ne_top
  have ht : Filter.Tendsto (fun n => K * c n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hc (Or.inr hK)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have h := inverseAverageError_lintegral_le m μ ν hprod π l hπ hl
      (hφ n) (hφm n) hB hB0 hTc.measurableSet hT y (hC y hy) (hbound n)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [K]
    ac_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseTransferIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse-coefficient transfer

The inverse transfer is the negative inverse linear map applied to the
whole-fiber average. Its cocycle identity holds almost everywhere for each
fixed group element, exactly as required for an L² cocycle.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]

omit [CompleteSpace W] in
/-- The constructed inverse transfer belongs to the actual L² space. -/
theorem inverseTheta_memLp
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseTheta (normalizedRestriction m B) A π l φ) 2 ν :=
  (A.symm.toContinuousLinearMap.comp_memLp'
    (inverseAveragedTransfer_memLp m μ ν hprod π l hπ hl hφ hB hB0)).neg

/-- The inverse transfer identity is derived on almost every fiber, with no
assertion of a simultaneous exceptional set for all group elements. -/
theorem inverseTheta_identity_ae
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (y : G) :
    ∀ᵐ p ∂ν, pairHeight π y p +
      inverseTheta (normalizedRestriction m B) A π l φ (normalizedTranslate y p) -
      inverseTheta (normalizedRestriction m B) A π l φ p =
      A.symm (π y).toAdd - A.symm (inverseAverageError (normalizedRestriction m B) π l φ y p) := by
  let β := normalizedRestriction m B
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  have hD := inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0
  have hS := inverseFiberTransfer_shift_memLp ν β π l hl φ hD y
  have hDi := hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hSi := hS.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  filter_upwards [(integrable_prod_iff hDi.aestronglyMeasurable).mp hDi |>.1,
    (integrable_prod_iff hSi.aestronglyMeasurable).mp hSi |>.1] with p hpD hpS
  have h := inverseAveragedTransfer_identity β π l φ y p hpS hpD
  rw [hlA] at h
  exact inverse_transfer_linear_coefficient A h

/-- Squared inverse-cocycle errors have at most the squared operator norm
loss when compared with the averaged fiber error. -/
theorem inverseCocycleError_lintegral_le
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (y : G) :
    (∫⁻ p, ‖inverseCocycleError (normalizedRestriction m B) A π l φ y p‖ₑ ^ 2 ∂ν) ≤
      ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2 *
        ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν := by
  have hi := inverseTheta_identity_ae m μ ν hprod A π l hπ hl hlA hφ hB hB0 y
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2 *
        ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hi] with p hp
      have he : inverseCocycleError (normalizedRestriction m B) A π l φ y p =
          -A.symm (inverseAverageError (normalizedRestriction m B) π l φ y p) := by
        unfold inverseCocycleError
        rw [hp]
        abel
      rw [he, enorm_neg]
      let r := inverseAverageError (normalizedRestriction m B) π l φ y p
      have hn : ‖A.symm r‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖r‖ :=
        A.symm.toContinuousLinearMap.le_opNorm r
      simp only [← ofReal_norm]
      change (ENNReal.ofReal ‖A.symm r‖) ^ 2 ≤
        (ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖) ^ 2 * (ENNReal.ofReal ‖r‖) ^ 2
      rw [← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_pow (norm_nonneg _) 2,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (mul_pow _ _ 2)
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- Compact-uniform vanishing of averaged fiber errors gives the same
vanishing for the actual inverse-coefficient cocycle. -/
theorem inverseCocycleError_tendsto_uniform
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    {B Q : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0)
    (hR : Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseCocycleError (normalizedRestriction m B) A π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0) := by
  let K := ENNReal.ofReal ‖A.symm.toContinuousLinearMap‖ ^ 2
  have ht : Filter.Tendsto (fun n => K * (⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hR
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    refine (inverseCocycleError_lintegral_le m μ ν hprod A π l hπ hl hlA (hφ n) hB hB0 y).trans ?_
    apply mul_le_mul_right
    exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InverseCoupling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse coupling with the prescribed inverse coefficient

Compact-uniform approximation of the forward height cocycle transfers to
the inverse section, with precisely the inverse linear coefficient. The
measure and the square-integrable transfer functions are constructed from
the pair-space charts and whole-fiber averages.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
  [MeasurableSpace W] [BorelSpace W]

/-- The manuscript's inverse-coupling construction, in the equivalent
squared-L² compact-uniform formulation. The inverse-section measure and all
inverse transfer functions are produced by the proof. -/
theorem inverseCoupling
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W)
    (hφ : ∀ n, MemLp (φ n) 2 μ) (hφm : ∀ n, Measurable (φ n))
    (happrox : ∀ T : Set G, IsCompact T →
      Filter.Tendsto (fun n => ⨆ t ∈ T,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∃ ν : Measure (NormalizedPair G Λ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      ∃ θ : ℕ → NormalizedPair G Λ → W, (∀ n, MemLp (θ n) 2 ν) ∧
        ∀ Q : Set G, IsCompact Q →
          Filter.Tendsto (fun n => ⨆ y ∈ Q,
            ∫⁻ p, ‖pairHeight π y p + θ n (normalizedTranslate y p) - θ n p -
              A.symm (π y).toAdd‖ₑ ^ 2 ∂ν) Filter.atTop (nhds 0) := by
  obtain ⟨ν, hνfin, hν0, hνinv, hprod⟩ := exists_inverseSection_measure m μ
  let := hνfin
  let := hνinv
  obtain ⟨B, hB, hB0⟩ := (Measure.Regular.exists_isCompact_not_null (μ := m)).mpr (NeZero.ne m)
  let θ := fun n => inverseTheta (normalizedRestriction m B) A π l (φ n)
  refine ⟨ν, hνfin, hν0, hνinv, θ, ?_, ?_⟩
  · intro n
    exact inverseTheta_memLp m μ ν hprod A π l hπ hl (hφ n) hB hB0
  · intro Q hQ
    obtain ⟨C, T, _hC, hT, hcenters, hincrements⟩ :=
      exists_inverse_compact_regions (Λ := Λ) hQ hB
    have hR := inverseAverageError_tendsto_uniform m μ ν hprod π l hπ hl φ hφ hφm
      hB hB0 hT hincrements hcenters (happrox T hT)
      (fun n t ht => le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    exact inverseCocycleError_tendsto_uniform m μ ν hprod A π l hπ hl hlA φ hφ hB hB0 hR

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_L2LabelDistance
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance to a finite label set from one L2 approximation

The comparison uses any one label known on the fixed component. Its
conclusion takes distance to the whole set and needs no selection of labels.
-/

namespace PolycyclicRecognition

open MeasureTheory Metric
open scoped ENNReal

variable {X W : Type} [MeasurableSpace X] [NormedAddCommGroup W]

/-- An L2 approximation to one point of a set bounds the average distance
to the whole set on a probability space. -/
theorem lintegral_infDist_le_L2 (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → W) (v : Lp W 2 μ) {S : Set W} {w : W} (hw : w ∈ S)
    (hv : (v : X → W) =ᵐ[μ] fun x => f x - w) :
    ∫⁻ x, ENNReal.ofReal (infDist (f x) S) ∂μ ≤ ENNReal.ofReal ‖v‖ := by
  calc
    _ ≤ ∫⁻ x, ‖v x‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hv] with x hx
      rw [← ofReal_norm, hx]
      apply ENNReal.ofReal_le_ofReal
      simpa only [dist_eq_norm] using infDist_le_dist_of_mem hw
    _ = eLpNorm v 1 μ := (eLpNorm_one_eq_lintegral_enorm).symm
    _ ≤ eLpNorm v 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
    _ = ENNReal.ofReal ‖v‖ := by rw [ofReal_norm, Lp.enorm_def]

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact-uniform stationary coboundary approximations

The Cornulier–Tessera reduced-cohomology theorem gives compact-uniform
coboundary approximation vectors for the zero-mean Hilbert representation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- On a proper metric group, compact-uniform approximations can be chosen
as one sequence using the integer-radius compact exhaustion. -/
theorem coboundary_approximation_sequence
    {G E : Type} [Group G] [MetricSpace G] [ProperSpace G]
    [NormedAddCommGroup E] [DistribMulAction G E]
    (b : G → E)
    (happrox : ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε) :
    ∃ φ : ℕ → E, ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q, ‖b q + q • φ n - φ n‖ ≤ ε := by
  choose φ hφ using fun n : ℕ => happrox (Metric.closedBall (1 : G) n)
    (isCompact_closedBall 1 n) (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨φ, fun Q hQ ε hε => ?_⟩
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall (1 : G)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have heps : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := heps.eventually (gt_mem_nhds hε)
  filter_upwards [Filter.eventually_ge_atTop N, hsmall] with n hn hεn
  intro q hq
  refine (hφ n q ?_).trans hεn.le
  exact (Metric.closedBall_subset_closedBall (hN.trans (by exact_mod_cast hn))) (hR hq)

/-- One sequence of ambient approximation vectors works on every compact
set for the stationary cocycle and its actual mean slope. -/
theorem stationary_coboundary_approximation_sequence
    {G X W : Type} [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [MulAction G X] [ContinuousSMul G X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (b : G → Lp W 2 μ) (hbcont : Continuous b) (hb : IsCocycle b) :
    ∃ φ : ℕ → Lp W 2 μ, ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q,
        ‖b q + stationaryPullback μ q (φ n) - φ n -
          Lp.const 2 μ (l2MeanSlope μ b hb q).toAdd‖ ≤ ε := by
  have hact (v : ZeroMeanL2 (W := W) μ) : Continuous (fun g : G => g • v) := by
    exact ((continuous_stationaryPullback μ).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _
  obtain ⟨φ, hφ⟩ := coboundary_approximation_sequence (centeredL2Cocycle μ b)
    (hvan (zeroMeanL2_no_fixed μ) hact (centeredL2Cocycle μ b)
      (continuous_centeredL2 μ b hbcont) (isCocycle_centeredL2 μ b hb))
  refine ⟨fun n => (φ n).val, fun Q hQ ε hε => ?_⟩
  filter_upwards [hφ Q hQ ε hε] with n hn
  intro q hq
  have hh := hn q hq
  change ‖(b q - Lp.const 2 μ (stationaryL2Mean μ (b q))) +
    stationaryPullback μ q (φ n).val - (φ n).val‖ ≤ ε at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  change b q + stationaryPullback μ q (φ n).val - (φ n).val -
    Lp.const 2 μ (stationaryL2Mean μ (b q)) = _
  abel

/-- The squared extended norm integral of an L² vector is its squared norm. -/
theorem lintegral_enorm_sq_L2 {X W : Type} [MeasurableSpace X]
    [NormedAddCommGroup W] (μ : Measure X) (f : Lp W 2 μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal ‖f‖ ^ 2 := by
  have h := congrArg (fun r : ℝ≥0∞ => r ^ (2 : ℝ))
    (eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (f := f) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at h
  rw [← Lp.enorm_def, ← ofReal_norm] at h
  simpa only [ENNReal.rpow_ofNat] using h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable approximation of the actual pair-height cocycle -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

/-- A representative of an L² transfer gives exactly the pointwise defect
of the height cocycle, up to the unavoidable null set for a fixed group element. -/
theorem pairTransferDefect_ae_L2
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (v : Lp W 2 μ) (φ : NormalizedPair G Λ → W) (hv : v =ᵐ[μ] φ) (g : G) :
    (pairHeightL2 μ π hπ g + stationaryPullback μ g v - v -
      Lp.const 2 μ (l g).toAdd : Lp W 2 μ) =ᵐ[μ] pairTransferDefect π l φ g := by
  have hb : pairHeightL2 μ π hπ g =ᵐ[μ] pairHeight π g :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)
  have hpull : stationaryPullback μ g v =ᵐ[μ] fun p => v (g⁻¹ • p) :=
    Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g⁻¹ μ)
  have hvpull := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp hv
  filter_upwards [hb, hpull, hvpull, hv,
    Lp.coeFn_add (pairHeightL2 μ π hπ g) (stationaryPullback μ g v),
    Lp.coeFn_sub (pairHeightL2 μ π hπ g + stationaryPullback μ g v) v,
    Lp.coeFn_sub (pairHeightL2 μ π hπ g + stationaryPullback μ g v - v)
      (Lp.const 2 μ (l g).toAdd), Lp.coeFn_const 2 μ (l g).toAdd]
    with p hb hpull hvpull hv hadd hsub hsub' hc
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply] at *
  rw [hsub', hsub, hadd, hb, hpull, hvpull, hv, hc]
  change pairHeight π g p + φ (normalizedTranslate g⁻¹⁻¹ p) - φ p - (l g).toAdd = _
  simp only [inv_inv, pairTransferDefect]

/-- Uniformly small nonnegative real errors have uniformly vanishing squared
extended-real errors. This handles the supremum over an entire compact set. -/
theorem uniform_ofReal_sq_tendsto {T : Type} (f : ℕ → T → ℝ) (Q : Set T)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q, f n q ≤ ε) :
    Filter.Tendsto (fun n => ⨆ q ∈ Q, ENNReal.ofReal (f n q) ^ 2)
      Filter.atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have ht : Filter.Tendsto (fun k : ℕ =>
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.pow (n := 2)
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hsmall (1 / ((k : ℝ) + 1)) (by positivity)] with n hn
  refine iSup_le fun q => iSup_le fun hq => (pow_le_pow_left₀ (by positivity) ?_ 2).trans hk.le
  exact ENNReal.ofReal_le_ofReal (hn q hq)

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

omit [Nonempty B] in
theorem basisTemplateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) (b : B) :
    D.basisTemplateSupport ((fun x => x + w) '' E) b = D.basisTemplateSupport E b := by
  simp only [basisTemplateSupport, D.weightSupport_translate hE hne, mul_add,
    Finset.sum_add_distrib, D.balanced, add_zero]

theorem templateSupport_translate {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (w : W) : D.templateSupport ((fun x => x + w) '' E) = D.templateSupport E := by
  simp only [templateSupport, D.basisTemplateSupport_translate hE hne]

end PolycyclicRecognition.SupportDatum

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoarseFlowBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse bounds along actual one-parameter subgroups

Continuity and the homomorphism law suffice for the path-mesh estimates.
The additive constant accommodates short parameter intervals without an
extra Riemannian regularity assumption on the ambient metric.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem continuous_flow_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, dist 1 (d t) ≤ C * (1 + |t|) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).bddAbove_image
    (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have hh := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num))
    simpa [hzero] using hh
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨C, hC0, ?_⟩
  intro t
  let n := ⌊|t|⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊|t|⌋₊)
  have htn : |t| ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one |t|).le
  have hnt : (n : ℝ) ≤ |t| + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (abs_nonneg t)) 1
  have hsabs : |t / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr htn
  have hs : t / n ∈ Icc (-1 : ℝ) 1 := abs_le.mp hsabs
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have he : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [he]
  exact (dist_one_pow_le _ _).trans ((mul_le_mul_of_nonneg_left hlocal hn.le).trans
    (by nlinarith))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairMeanControl
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control of the actual stationary mean

The common Lipschitz constant of normalized pairs bounds their height
profiles, and hence bounds the homomorphism obtained by integration.
Consequently the actual averaged homomorphism kills every root flow.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory LieAlgebra LieModule
open scoped NNReal Manifold

section Mean

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {Λ K : ℝ≥0}

omit [ProperSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedSpace ℝ W] [CompleteSpace W] in
/-- Pointwise height control uses the forward normalization at the identity. -/
theorem norm_pairHeight_le (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g : G) (p : NormalizedPair G Λ) :
    ‖pairHeight π g p‖ ≤ (K : ℝ) * Λ * dist 1 g := by
  have h₁ := hπ.dist_le_mul (p.val.1 g) (p.val.1 1)
  have h₂ := p.property.1.1.dist_le_mul g 1
  rw [p.property.2] at h₂
  rw [p.property.2, map_one] at h₁
  change dist (pairHeight π g p) 0 ≤ _ at h₁
  rw [dist_zero_right] at h₁
  exact h₁.trans (by simpa only [dist_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left h₂ K.coe_nonneg)

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

attribute [local instance] stationaryL2Action

omit [CompleteSpace W] in
theorem continuous_normalizedPairMeanSlope (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (fun g => (normalizedPairMeanSlope μ π hπ g).toAdd) :=
  (stationaryL2Mean μ).continuous.comp (continuous_pairHeightL2 μ π hπ)

omit [CompleteSpace W] in
/-- Integration preserves the common linear metric bound. -/
theorem norm_normalizedPairMeanSlope_le (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd)) (g : G) :
    ‖(normalizedPairMeanSlope μ π hπ.continuous g).toAdd‖ ≤
      (K : ℝ) * Λ * dist 1 g := by
  change ‖∫ p, pairHeightL2 μ π hπ.continuous g p ∂μ‖ ≤ _
  have hae : (pairHeightL2 μ π hπ.continuous g : NormalizedPair G Λ → W) =ᵐ[μ]
      pairHeight π g := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ
        (pairHeightProfile π hπ.continuous g)
  calc
    _ = ‖∫ p, pairHeight π g p ∂μ‖ := congrArg norm (integral_congr_ae hae)
    _ ≤ _ := by
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (norm_pairHeight_le π hπ g))

end Mean

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairLabelFunctions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous uniformly bounded label-distance observables -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal ENNReal

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}

omit [IsTopologicalGroup G] [IsIsometricSMul G G] in
/-- For each fixed scale the observable is continuous on the compact pair section. -/
theorem continuous_pair_label_distance
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (g : G) (r : ℝ) (S : Set W) :
    Continuous (fun p : NormalizedPair G Λ => infDist (r⁻¹ • pairHeight π g p) S) :=
  (continuous_infDist_pt S).comp ((pairHeightProfile π hπ g).continuous.const_smul _)

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] in
/-- Linear growth of the sampled group element gives a common bound at all
scales at least one, using any fixed member of the comparison set. -/
theorem pair_label_distance_le
    (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd))
    {g : G} {r R : ℝ} (hr : 1 ≤ r) (_hR : 0 ≤ R) (hg : dist 1 g ≤ R * r)
    {S : Set W} {w : W} (hw : w ∈ S) (p : NormalizedPair G Λ) :
    infDist (r⁻¹ • pairHeight π g p) S ≤ (K : ℝ) * Λ * R + ‖w‖ := by
  have hr0 : 0 < r := by linarith
  have hn : ‖r⁻¹ • pairHeight π g p‖ ≤ (K : ℝ) * Λ * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    calc
      _ ≤ r⁻¹ * ((K : ℝ) * Λ * dist 1 g) :=
        mul_le_mul_of_nonneg_left (norm_pairHeight_le π hπ g p) (inv_nonneg.mpr hr0.le)
      _ ≤ r⁻¹ * ((K : ℝ) * Λ * (R * r)) := by gcongr
      _ = _ := by field_simp
  exact (infDist_le_dist_of_mem hw).trans (by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (add_le_add hn le_rfl))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateComparisonTranslation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the choice of origin from template comparison -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (P : PolycyclicRecognition.SupportDatum W I B)

/-- Translation invariance extends the comparison for templates containing
zero to every nonempty compact convex template. -/
theorem templateSupport_le_of_zero_mem (A : W →L[ℝ] W)
    (h : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A '' C))
    (C : Set W) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) :
    P.templateSupport C ≤ P.templateSupport (A '' C) := by
  obtain ⟨x, hx⟩ := hne
  let D := (fun y => y + -x) '' C
  have hD : IsCompact D := hC.image (continuous_id.add_const _)
  have hDv : Convex ℝ D := by
    simpa only [add_comm] using hconv.translate (-x)
  have hD0 : (0 : W) ∈ D := ⟨x, hx, add_neg_cancel x⟩
  have hle := h D hD hDv hD0
  have hne : C.Nonempty := ⟨x, hx⟩
  have hPD : P.templateSupport D = P.templateSupport C :=
    P.templateSupport_translate hC hne (-x)
  have himage : A '' D = (fun y => y + -(A x)) '' (A '' C) := by
    simp only [D, image_image, map_add, map_neg]
  rw [hPD, himage, P.templateSupport_translate (hC.image A.continuous) (hne.image A)] at hle
  exact hle

/-- Forward and inverse comparisons force preservation of the full
template functional, using only comparisons for templates through zero. -/
theorem template_symmetry_of_zero_mem_comparisons (A : W ≃L[ℝ] W)
    (hf : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A '' C))
    (hi : ∀ C : Set W, IsCompact C → Convex ℝ C → (0 : W) ∈ C →
      P.templateSupport C ≤ P.templateSupport (A.symm '' C)) :
    A.toLinearEquiv ∈ templateSymmetryGroup P := by
  intro C hc hn hv
  have hf' := P.templateSupport_le_of_zero_mem A.toContinuousLinearMap hf C hc hn hv
  have hi' := P.templateSupport_le_of_zero_mem A.symm.toContinuousLinearMap hi
    (A '' C) (hc.image A.continuous) (hn.image A) (hv.linear_image A.toLinearMap)
  have he : A.symm '' (A '' C) = C := by
    simp only [image_image, ContinuousLinearEquiv.symm_apply_apply, image_id']
  change P.templateSupport (A '' C) ≤ P.templateSupport (A.symm '' (A '' C)) at hi'
  rw [he] at hi'
  exact le_antisymm hi' hf'

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ErgodicMixtureLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded limits through the published ergodic decomposition

Setwise barycenters are enough for the stationary-increment application.
No measurable selection of a label on the components is needed.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X : Type} [MeasurableSpace X]

/-- Extend a setwise decomposition to every nonnegative measurable integrand. -/
theorem lintegral_eq_of_setwise_barycenter (μ : Measure X) (κ : X → Measure X)
    (hκ : ∀ s : Set X, MeasurableSet s → Measurable (fun x => κ x s))
    (hbary : ∀ s : Set X, MeasurableSet s → μ s = ∫⁻ x, κ x s ∂μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ y, f y ∂κ x ∂μ := by
  have hm : Measurable κ := Measure.measurable_of_measurable_coe κ hκ
  have heq : μ.bind κ = μ := by
    ext s hs
    rw [Measure.bind_apply hs hm.aemeasurable, ← hbary s hs]
  rw [← heq, Measure.lintegral_bind hm.aemeasurable hf.aemeasurable, heq]

/-- Uniformly bounded componentwise convergence passes through a probability
barycenter, with the component map kept fixed throughout the limit. -/
theorem tendsto_lintegral_of_componentwise_bounded
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → Measure X)
    (hκ : ∀ s : Set X, MeasurableSet s → Measurable (fun x => κ x s))
    (hbary : ∀ s : Set X, MeasurableSet s → μ s = ∫⁻ x, κ x s ∂μ)
    {ι : Type} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : ∀ᶠ n in l, ∀ x, ∫⁻ y, f n y ∂κ x ≤ B)
    (hlim : ∀ x, Tendsto (fun n => ∫⁻ y, f n y ∂κ x) l (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) l (𝓝 0) := by
  have hm : Measurable κ := Measure.measurable_of_measurable_coe κ hκ
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _ : X => B)
    (Eventually.of_forall (fun n => (Measure.measurable_lintegral (hf n)).comp hm))
    (hbound.mono (fun _ hn => Eventually.of_forall hn)) (by simpa using hB)
    (Eventually.of_forall hlim)
  have heq (n : ι) := lintegral_eq_of_setwise_barycenter μ κ hκ hbary (f n) (hf n)
  simpa only [Function.comp_apply, ← heq, lintegral_zero] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairMeanApproximation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact coboundaries with the actual averaged homomorphism retained -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The published reduced-cohomology input supplies measurable compact-uniform
transfers for the concrete mean, whose metric control is already proved. -/
theorem normalizedPairMean_coboundary_approximation
    {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    ∃ φ : ℕ → NormalizedPair G Λ → W,
        (∀ n, MemLp (φ n) 2 μ) ∧ (∀ n, Measurable (φ n)) ∧
        ∀ Q : Set G, IsCompact Q →
          Filter.Tendsto (fun n => ⨆ t ∈ Q,
            ∫⁻ p, ‖pairTransferDefect π (normalizedPairMeanSlope μ π hπ) (φ n) t p‖ₑ ^ 2 ∂μ)
            Filter.atTop (nhds 0) := by
  let b := pairHeightL2 μ π hπ
  have hb : IsCocycle b := isCocycle_pairHeightL2 μ π hπ
  let l := l2MeanSlope μ b hb
  obtain ⟨ψ, hψ⟩ := stationary_coboundary_approximation_sequence μ hvan b
    (continuous_pairHeightL2 μ π hπ) hb
  let φ : ℕ → NormalizedPair G Λ → W :=
    fun n => (Lp.aestronglyMeasurable (ψ n)).mk (ψ n)
  have hae (n : ℕ) : ψ n =ᵐ[μ] φ n :=
    (Lp.aestronglyMeasurable (ψ n)).ae_eq_mk
  refine ⟨φ, fun n => (Lp.memLp (ψ n)).ae_eq (hae n),
    fun n => (Lp.aestronglyMeasurable (ψ n)).measurable_mk, ?_⟩
  intro Q hQ
  have heq (n : ℕ) (t : G) :
      (∫⁻ p, ‖pairTransferDefect π (normalizedPairMeanSlope μ π hπ) (φ n) t p‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal ‖b t + stationaryPullback μ t (ψ n) - ψ n -
        Lp.const 2 μ (l t).toAdd‖ ^ 2 := by
    rw [← lintegral_enorm_sq_L2]
    exact lintegral_congr_ae
      ((pairTransferDefect_ae_L2 μ π l hπ (ψ n) (φ n) (hae n) t).symm.fun_comp
        (fun w => ‖w‖ₑ ^ 2))
  simp_rw [heq]
  exact uniform_ofReal_sq_tendsto _ Q (hψ Q hQ)


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairMeasureScaling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing a finite stationary measure

The inverse coupling produces a finite nonzero measure. Its probability
normalization retains the same sublinear error and therefore the same
prescribed inverse coefficient.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsIsometricSMul G G] in
/-- The pointwise error and the Hilbert error agree for every finite measure. -/
theorem eLpNorm_pairHeight_error_finite
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    eLpNorm (fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd) 2 μ =
      ENNReal.ofReal ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)).sub
    (Lp.coeFn_const 2 μ (l g).toAdd)).symm.trans (Lp.coeFn_sub _ _).symm

omit [IsIsometricSMul G G] in
/-- Scaling the measure scales every height-error norm by one fixed factor. -/
theorem norm_pairHeight_error_smul_measure
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (c : ℝ≥0∞) [IsFiniteMeasure (c • μ)]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    ‖pairHeightL2 (c • μ) π hπ g - Lp.const 2 (c • μ) (l g).toAdd‖ =
      (c ^ (1 / 2 : ℝ)).toReal * ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  have h := eLpNorm_smul_measure_of_ne_top
    (μ := μ) (f := fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd)
    (p := 2) (by norm_num) (c := c)
  rw [eLpNorm_pairHeight_error_finite, eLpNorm_pairHeight_error_finite] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hr

omit [IsIsometricSMul G G] in
/-- Sublinearity survives every finite scaling of the stationary measure. -/
theorem pairHeight_sublinear_smul_measure
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (c : ℝ≥0∞) [IsFiniteMeasure (c • μ)]
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 (c • μ) π hπ g - Lp.const 2 (c • μ) (l g).toAdd‖ ≤
        ε * dist 1 g + B := by
  intro ε hε
  let C := (c ^ (1 / 2 : ℝ)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  obtain ⟨B, hB, hb⟩ := hsub (ε / (C + 1)) (div_pos hε (by positivity))
  refine ⟨C * B, mul_nonneg hC hB, fun g => ?_⟩
  rw [norm_pairHeight_error_smul_measure]
  have hh := mul_le_mul_of_nonneg_left (hb g) hC
  have hc : C * (ε / (C + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  calc
    _ ≤ C * (ε / (C + 1) * dist 1 g + B) := hh
    _ = C * (ε / (C + 1)) * dist 1 g + C * B := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc dist_nonneg) le_rfl

/-- A finite nonzero invariant measure can be normalized without changing
its prescribed sublinear slope. -/
theorem exists_probability_with_same_pairHeight_slope
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (hμ : μ ≠ 0)
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∃ ν : Measure (NormalizedPair G Λ), ∃ hν : IsProbabilityMeasure ν,
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      let := hν
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 ν π hπ g - Lp.const 2 ν (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  have hmass : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  let ν := (μ univ)⁻¹ • μ
  have hν : IsProbabilityMeasure ν := by
    constructor
    change ((μ univ)⁻¹ • μ) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_lt_top μ univ).ne
  let := hν
  refine ⟨ν, hν, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
  exact pairHeight_sublinear_smul_measure μ (μ univ)⁻¹ π l hπ hsub

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairStationaryIncrement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed stationary slope gives increments close to the finite label set -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

omit [IsIsometricSMul G G] in
/-- Normalized increments inherit an L2 distance bound from any one label. -/
theorem lintegral_normalized_pair_label_distance_le
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (g : G) {r : ℝ} (hr : 0 < r) {S : Set W} {w : W} (hw : w ∈ S) :
    ∫⁻ p, ENNReal.ofReal (infDist (r⁻¹ • pairHeight π g p) S) ∂μ ≤
      ENNReal.ofReal (r⁻¹ * ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)‖) := by
  let e := pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)
  let v := r⁻¹ • e
  have hae : (v : NormalizedPair G Λ → W) =ᵐ[μ]
      fun p => r⁻¹ • pairHeight π g p - w := by
    filter_upwards [Lp.coeFn_smul r⁻¹ e,
      Lp.coeFn_sub (pairHeightL2 μ π hπ g) (Lp.const 2 μ (r • w)),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g),
      Lp.coeFn_const 2 μ (r • w)] with p hs he hp hc
    change pairHeightL2 μ π hπ g p = pairHeight π g p at hp
    rw [hs]
    change r⁻¹ • ((pairHeightL2 μ π hπ g - Lp.const 2 μ (r • w)) p) = _
    rw [he]
    simp only [Pi.sub_apply]
    rw [hp, hc]
    change r⁻¹ • (pairHeight π g p - r • w) = _
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have h := lintegral_infDist_le_L2 μ _ v hw hae
  simpa only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] using h

omit [IsIsometricSMul G G] in
/-- The fixed-measure sublinear estimate implies convergence to the whole
label set along every linearly bounded family with the prescribed slope. -/
theorem normalized_pair_increments_tendsto_labels
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (g : ℝ → G) {R : ℝ} (hR : 0 ≤ R)
    (hsize : ∀ r, 1 ≤ r → dist 1 (g r) ≤ R * r)
    {S : Set W} {w : W} (hw : w ∈ S)
    (hslope : ∀ r, 1 ≤ r → (l (g r)).toAdd = r • w) :
    Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (g r) p) S) ∂μ) atTop (𝓝 0) := by
  let e := fun x => pairHeightL2 μ π hπ x - Lp.const 2 μ (l x).toAdd
  have hlim : Tendsto (fun r : ℝ => r⁻¹ * ‖e (g r)‖) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have hnonneg : 0 ≤ r⁻¹ * ‖e (g r)‖ := mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
      exact ha.trans_le hnonneg
    · intro ε hε
      obtain ⟨r₀, _, hb⟩ := uniform_sublinear_on_balls (fun x : G => dist 1 x) hsub hR
        (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop (max 1 r₀)] with r hr
      have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
      have hr0 : 0 < r := by linarith
      have h := mul_le_mul_of_nonneg_left
        (hb r ((le_max_right _ _).trans hr) (g r) (hsize r hr1)) (inv_nonneg.mpr hr0.le)
      have he : r⁻¹ * ‖e (g r)‖ ≤ ε / 2 := by
        simpa only [e, ← mul_assoc, mul_left_comm r⁻¹, inv_mul_cancel₀ hr0.ne', mul_one] using h
      linarith
  have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal (r⁻¹ * ‖e (g r)‖)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hb := lintegral_normalized_pair_label_distance_le μ π hπ (g r)
    (by linarith : 0 < r) hw
  simpa only [e, hslope r hr] using hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairSublinear
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear height errors from the coupled transfers

The finite invariant measure on the inverse section need not be ergodic.
The transfers already constructed there suffice for the same word estimate.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]

/-- Subtracting any continuous height homomorphism preserves the cocycle
identity, independently of any ergodicity or averaging assertion. -/
theorem isCocycle_pairHeight_sub_hom
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    IsCocycle (fun g => pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd) := by
  intro g h
  have hb := isCocycle_pairHeightL2 μ π hπ g h
  change pairHeightL2 μ π hπ (g * h) - Lp.const 2 μ (l (g * h)).toAdd =
    (pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd) +
      stationaryPullback μ g (pairHeightL2 μ π hπ h - Lp.const 2 μ (l h).toAdd)
  rw [hb, map_sub, stationaryPullback_const_finite, map_mul l]
  simp only [toAdd_mul, map_add]
  change pairHeightL2 μ π hπ g + stationaryPullback μ g (pairHeightL2 μ π hπ h) -
    (Lp.const 2 μ (l g).toAdd + Lp.const 2 μ (l h).toAdd) = _
  abel

/-- A compact-uniform squared-error estimate gives an actual small
coboundary in the Hilbert space, for a finite invariant measure. -/
theorem pairHeight_coboundary_of_squared_errors
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (Q : Set G)
    (happrox : Filter.Tendsto (fun n => ⨆ t ∈ Q,
      ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ v : Lp W 2 μ, ∀ q ∈ Q,
      ‖(pairHeightL2 μ π hπ q - Lp.const 2 μ (l q).toAdd) + q • v - v‖ ≤ ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp happrox
    (ENNReal.ofReal (ε ^ 2)) (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε))).exists
  let v := (hφ n).toLp (φ n)
  refine ⟨v, fun q hq => ?_⟩
  let e := pairHeightL2 μ π hπ q + stationaryPullback μ q v - v -
    Lp.const 2 μ (l q).toAdd
  have heq : (∫⁻ p, ‖pairTransferDefect π l (φ n) q p‖ₑ ^ 2 ∂μ) =
      ENNReal.ofReal ‖e‖ ^ 2 := by
    rw [← lintegral_enorm_sq_L2]
    exact lintegral_congr_ae
      ((pairTransferDefect_ae_L2 μ π l hπ v (φ n) (hφ n).coeFn_toLp q).symm.fun_comp
        (fun w => ‖w‖ₑ ^ 2))
  have he : ENNReal.ofReal (‖e‖ ^ 2) ≤ ENNReal.ofReal (ε ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg e), ← heq]
    calc
      _ ≤ ⨆ t ∈ Q, ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ :=
        le_iSup_of_le q (le_iSup_of_le hq le_rfl)
      _ ≤ _ := hn
  have hsq := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ε)).mp he
  have he' : ‖e‖ ≤ ε := by nlinarith [norm_nonneg e]
  convert he' using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp [e]
  change (pairHeightL2 μ π hπ q - Lp.const 2 μ (l q).toAdd) +
    stationaryPullback μ q v - v = _
  abel

/-- Compact-uniform transfer errors imply the global sublinear word bound.
This applies directly to the finite measure constructed by inverse coupling. -/
theorem pairHeight_sublinear_of_squared_errors
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (Q : Set G) (length : G → ℝ) (hlen : ∀ g, 0 ≤ length g)
    {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ w : List G, (∀ q ∈ w, q ∈ Q) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ a * length g + a)
    (happrox : Filter.Tendsto (fun n => ⨆ t ∈ Q,
      ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * length g + B := by
  exact (isCocycle_pairHeight_sub_hom μ π l hπ).sublinear_of_coboundary_approximation
    Q length hlen ha hword (pairHeight_coboundary_of_squared_errors μ π l hπ φ hφ Q happrox)

/-- For a proper group with minimizing paths, compact-uniform transfer
approximation alone supplies metric sublinearity. -/
theorem pairHeight_sublinear_of_minimizing_paths
    (π l : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W) (hφ : ∀ n, MemLp (φ n) 2 μ)
    (happrox : ∀ Q : Set G, IsCompact Q →
      Filter.Tendsto (fun n => ⨆ t ∈ Q,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B := by
  apply pairHeight_sublinear_of_squared_errors μ π l hπ φ hφ (Metric.closedBall 1 1)
    (fun g => dist 1 g) (fun _ => dist_nonneg) (a := 1) (by norm_num)
  · simpa using wordFactorization_of_minimizing_paths hpath
  · exact happrox _ (isCompact_closedBall 1 1)

/-- The actual inverse coupling supplies a sublinear inverse height error
with exactly the inverse coefficient. No ergodicity of its finite measure
and no second reduced-cohomology hypothesis are required. -/
theorem inverseCoupling_sublinear
    {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
    [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
    [MeasurableSpace W] [BorelSpace W]
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (A : W ≃L[ℝ] W) (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hlA : ∀ g, (l g).toAdd = A (π g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W)
    (hφ : ∀ n, MemLp (φ n) 2 μ) (hφm : ∀ n, Measurable (φ n))
    (happrox : ∀ T : Set G, IsCompact T →
      Filter.Tendsto (fun n => ⨆ t ∈ T,
        ∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    ∃ ν : Measure (NormalizedPair G Λ), ∃ hν : IsFiniteMeasure ν, ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      letI := hν
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 ν π hπ g - Lp.const 2 ν (A.symm (π g).toAdd)‖ ≤
          ε * dist 1 g + B := by
  obtain ⟨ν, hν, hν0, hνinv, θ, hθ, hθapprox⟩ :=
    inverseCoupling m μ A π l hπ hl hlA φ hφ hφm happrox
  let := hν
  let := hνinv
  let l' : G →* Multiplicative W := A.symm.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  refine ⟨ν, hν, hν0, hνinv, ?_⟩
  exact pairHeight_sublinear_of_minimizing_paths ν π l' hπ θ hθ hθapprox hpath

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryTemplateLabel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template-preserving labels from stationary volume comparison -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- Forward volume comparison and the actual coupled inverse force the
stationary mean into the finite template-symmetry group. -/
theorem exists_template_label_of_stationary_mean
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hΛ : 0 < (Λ : ℝ)) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (ψ : ℕ → NormalizedPair G Λ → W)
    (hψ : ∀ n, MemLp (ψ n) 2 μ) (hψm : ∀ n, Measurable (ψ n))
    (happrox : ∀ Q : Set G, IsCompact Q →
      Filter.Tendsto (fun n => ⨆ t ∈ Q,
        ∫⁻ p, ‖pairTransferDefect π l (ψ n) t p‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0)) :
    ∃ A : templateSymmetryGroup (M.supportIn T hunimod eW),
      ∀ g, (l g).toAdd = A.val (π g).toAdd := by
  obtain ⟨A₀, hA₀⟩ := M.exists_invertible_height_factor_of_stationary_mean
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
    hExp realize μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath
  let A := A₀.toContinuousLinearEquiv
  let l' : G →* Multiplicative W := A.symm.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  have hA (g : G) : (l g).toAdd = A (π g).toAdd := hA₀ g
  obtain ⟨ν, hν, hν0, hνinv, hνsub⟩ :=
    inverseCoupling_sublinear m μ A π l hπ hl hA ψ hψ hψm happrox hpath
  let := hν
  let := hνinv
  obtain ⟨σ, hσ, hσinv, hσsub⟩ :=
    exists_probability_with_same_pairHeight_slope ν hν0 π l' hπ hνsub
  let := hσ
  have hl' : Continuous fun g => (l' g).toAdd := A.symm.continuous.comp hπ
  have hbound' (g : G) : ‖(l' g).toAdd‖ ≤ ‖A.symm.toContinuousLinearMap‖ * K * dist 1 g := by
    have hπg : ‖(π g).toAdd‖ ≤ K * dist 1 g := by
      simpa only [map_one, toAdd_one, sub_zero, dist_comm] using hLip g 1
    calc
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖(π g).toAdd‖ :=
        A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * (K * dist 1 g) :=
        mul_le_mul_of_nonneg_left hπg (norm_nonneg _)
      _ = _ := by ring
  have hfwd (C : Set W) (hc : IsCompact C) (hv : Convex ℝ C) (h0 : (0 : W) ∈ C) :
      (M.supportIn T hunimod eW).templateSupport C ≤
        (M.supportIn T hunimod eW).templateSupport (A '' C) := by
    exact M.templateSupport_le_of_stationary_height_factor_m
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath
      A.toContinuousLinearMap hA C hc hv h0
  have hinv (C : Set W) (hc : IsCompact C) (hv : Convex ℝ C) (h0 : (0 : W) ∈ C) :
      (M.supportIn T hunimod eW).templateSupport C ≤
        (M.supportIn T hunimod eW).templateSupport (A.symm '' C) := by
    exact M.templateSupport_le_of_stationary_height_factor_m
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize σ l' hπ hl' hΛ hK (mul_nonneg (norm_nonneg _) hK) hLip hbound'
      hσsub b₀ hφ hpath A.symm.toContinuousLinearMap (fun _ => rfl) C hc hv h0
  have hiso := (M.supportIn T hunimod eW).template_symmetry_of_zero_mem_comparisons
    A hfwd hinv
  exact ⟨⟨A.toLinearEquiv, hiso⟩, hA⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanErgodicTemplateLabel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite stationary labels from the published reduced-cohomology input -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The precise published reduced-cohomology input gives a finite linear
label and the fixed-measure sublinear estimate on the actual pair space. -/
theorem exists_template_label_of_ergodic_probability
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    : ∃ A : templateSymmetryGroup (M.supportIn T hunimod eW),
      (∀ g, (normalizedPairMeanSlope μ π hLip.continuous g).toAdd = A.val (π g).toAdd) ∧
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 μ π hLip.continuous g - Lp.const 2 μ (A.val (π g).toAdd)‖ ≤
          ε * dist 1 g + B := by
  let l := normalizedPairMeanSlope μ π hLip.continuous
  have hl : Continuous fun g => (l g).toAdd := continuous_normalizedPairMeanSlope μ π hLip.continuous
  obtain ⟨ψ, hψ, hψm, happrox⟩ := normalizedPairMean_coboundary_approximation μ hvan π hLip.continuous
  have hsub := pairHeight_sublinear_of_minimizing_paths μ π l hLip.continuous ψ hψ happrox hpath
  have hbound : ∀ g, ‖(l g).toAdd‖ ≤ (K : ℝ) * Λ * dist 1 g :=
    norm_normalizedPairMeanSlope_le μ π hLip
  have hpoint : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ (K : ℝ) * dist x y := by
    intro x y
    simpa only [dist_eq_norm] using hLip.dist_le_mul x y
  obtain ⟨A, hA⟩ := M.exists_template_label_of_stationary_mean T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExp realize m μ l
    hLip.continuous hl hΛ K.coe_nonneg (mul_nonneg K.coe_nonneg Λ.coe_nonneg)
    hpoint hbound hsub b₀ hφ hpath ψ hψ hψm happrox
  refine ⟨A, hA, ?_⟩
  simpa only [hA] using hsub

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanErgodicTemplateIncrement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite stationary increments on actual Cartan rays -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- Along each actual Cartan exponential ray, normalized increments
approach the finite canonical label set for every fixed ergodic probability. -/
theorem increments_tendsto_template_labels_of_ergodic_probability
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : H) :
    Filter.Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
        (Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v))))) ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨A, _, hsub⟩ := M.exists_template_label_of_ergodic_probability
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
    hExp realize m μ hvan hΛ hLip b₀ hφ hpath
  let l : G →* Multiplicative W := A.val.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  let g : ℝ → G := fun r => Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd : Continuous g := continuous_exp_line_of_published_realization T Exp hExp realize v
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound g hd
    (by simp [g, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
  apply normalized_pair_increments_tendsto_labels μ π l hLip.continuous hsub g
    (R := 2 * C) (by positivity)
  · intro r hr
    have h := hb r
    rw [abs_of_nonneg (by linarith : 0 ≤ r)] at h
    exact h.trans (by nlinarith)
  · exact ⟨A, rfl⟩
  · intro r _
    change A.val (π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd = _
    simp only [hπExp, map_smul]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryTemplateIncrement
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stationary increments through the actual ergodic decomposition -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- Along each actual Cartan exponential ray, normalized increments
approach the finite canonical label set for every fixed invariant probability. The integrand uses the whole finite
label set, so no measurable choice of component labels is needed. -/
theorem increments_tendsto_template_labels_of_invariant_probability_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (ν : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure ν]
      [ErgodicSMul G (NormalizedPair G Λ) ν],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) ν))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : H) :
    Filter.Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
        (Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v))))) ∂μ)
      Filter.atTop (nhds 0) := by
  let w := eW (heightProjection T.character v)
  let S := Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) => A.val w)
  let f : ℝ → NormalizedPair G Λ → ℝ≥0∞ := fun r p =>
    ENNReal.ofReal (infDist (r⁻¹ • pairHeight π
      (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p) S)
  obtain ⟨κ, hκ, _, hbary⟩ := hdec μ inferInstance inferInstance
  have hκm : ∀ s : Set (NormalizedPair G Λ), MeasurableSet s →
      Measurable (fun x => κ x s) := fun s hs => (hbary s hs).1
  have hκb : ∀ s : Set (NormalizedPair G Λ), MeasurableSet s →
      μ s = ∫⁻ x, κ x s ∂μ := fun s hs => (hbary s hs).2
  let g : ℝ → G := fun r => Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd : Continuous g := continuous_exp_line_of_published_realization T Exp hExp realize v
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound g hd
    (by simp [g, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
  have hsize (r : ℝ) (hr : 1 ≤ r) : dist 1 (g r) ≤ (2 * C) * r := by
    have h := hb r
    rw [abs_of_nonneg (by linarith : 0 ≤ r)] at h
    exact h.trans (by nlinarith)
  have hw : w ∈ S := ⟨1, rfl⟩
  apply tendsto_lintegral_of_componentwise_bounded μ κ hκm hκb f
    (fun r => ENNReal.measurable_ofReal.comp
      (continuous_pair_label_distance π hLip.continuous (g r) r S).measurable)
    (B := ENNReal.ofReal ((K : ℝ) * Λ * (2 * C) + ‖w‖)) ENNReal.ofReal_ne_top
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
    intro x
    let := (hκ x).1
    calc
      ∫⁻ y, f r y ∂κ x ≤ ∫⁻ _, ENNReal.ofReal ((K : ℝ) * Λ * (2 * C) + ‖w‖) ∂κ x := by
        apply lintegral_mono
        intro p
        exact ENNReal.ofReal_le_ofReal
          (pair_label_distance_le π hLip hr (by positivity) (hsize r hr) hw p)
      _ = _ := by simp
  · intro x
    let := (hκ x).1
    let := (hκ x).2
    exact M.increments_tendsto_template_labels_of_ergodic_probability
      T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
      hExp realize m (κ x) (hvan (κ x)) hΛ hLip b₀ hφ hpath v

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability_oai := @OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability_oai
