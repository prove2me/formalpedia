-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le_m
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:22:45.460648+00:00
-- url     : https://prove2.me/submissions/1760a39d-08be-4a28-b643-3594fbaaedb6

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_coarse_path_polynomial_packing
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_controlled_increment_volume
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_tuple_lifts
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_terminal_product_exponent_le

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential-coordinate Haar measure

E. Le Donne, *Metric Lie Groups*, Graduate Texts in Mathematics 306,
Springer (2025), Theorem 9.4.7 (exponential coordinates) and Corollary 9.4.21.
https://doi.org/10.1007/978-3-031-98832-5_9

A global exponential chart identifies Haar measure on a simply connected
nilpotent Lie group with Lebesgue measure. The Euclidean determinant formula
then gives the volume of weighted boxes, including their scale factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

variable {E G} [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalize Haar measure using one exponential coordinate basis. -/
theorem exists_haar_exponential_cube_volume
    (haarInput : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n : ℕ} (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (μ : Measure G),
      (∀ x, chart x = Exp x) ∧ μ.IsHaarMeasure ∧
      ∀ R : ℝ, 0 ≤ R → μ (exponentialCoordinateBox Exp b R) = ENNReal.ofReal (2 * R) ^ n := by
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haarInput.2 Exp hExp hnil
  let f := Exp ∘ b.equivFun.symm
  let e : (Fin n → ℝ) ≃ₜ G :=
    b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = e := by
    funext t
    exact (hchart (b.equivFun.symm t)).symm
  have hmeas : MeasurableEmbedding f := by rw [hf]; exact e.measurableEmbedding
  refine ⟨chart, Measure.map f volume, hchart, hhaar n b, ?_⟩
  intro R hR
  rw [exponentialCoordinateBox_eq_cube_image Exp b R hR]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

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

omit [FiniteDimensional ℝ W] in
theorem templateSupport_le {E : Set W} {r : ℝ}
    (h : ∀ b, D.basisTemplateSupport E b ≤ r) : D.templateSupport E ≤ r :=
  Finset.sup'_le _ _ fun b _ => h b

omit [Nonempty B] in
/-- Nearby support positions change each letter exponent by at most the
operator norm of that letter times the error in position. -/
theorem weightSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ}
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ := by
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hneE i
  obtain ⟨y, hy, hxy⟩ := hnear x hx
  have hop := (D.weight i).toContinuousLinearMap.le_opNorm (x - y)
  change ‖D.weight i (x - y)‖ ≤ _ at hop
  rw [map_sub, Real.norm_eq_abs] at hop
  have hh := hop.trans (mul_le_mul_of_nonneg_left hxy
    (norm_nonneg (D.weight i).toContinuousLinearMap))
  have hy' := D.weight_le_weightSupport hF hy i
  rw [hsup]
  linarith [le_abs_self (D.weight i x - D.weight i y)]

omit [Nonempty B] in
theorem templateSupportConstant_nonneg : 0 ≤ D.templateSupportConstant :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem templateSupport_le_of_nearby {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ x ∈ E, ∃ y ∈ F, ‖x - y‖ ≤ δ) :
    D.templateSupport E ≤ D.templateSupport F + D.templateSupportConstant * δ := by
  apply D.templateSupport_le
  intro b
  have hc : (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) ≤
      D.templateSupportConstant := by
    unfold templateSupportConstant
    exact Finset.single_le_sum
      (f := fun b => ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖)
      (fun b _ => Finset.sum_nonneg
        (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))) (Finset.mem_univ b)
  calc
    D.basisTemplateSupport E b ≤
        ∑ i, (D.multiplicity b i : ℝ) *
          (D.weightSupport F i + ‖(D.weight i).toContinuousLinearMap‖ * δ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (D.weightSupport_le_of_nearby hE hneE hF hnear i) (Nat.cast_nonneg _))
    _ = D.basisTemplateSupport F b +
        (∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖) * δ := by
      simp only [basisTemplateSupport, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ ≤ D.templateSupport F + D.templateSupportConstant * δ :=
      add_le_add (D.basisTemplateSupport_le F b) (mul_le_mul_of_nonneg_right hc hδ)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth generator endpoint maps for varying polynomial laws

Each scheme is a fixed finite expression in the bracket, generators, and
its variable amplitudes. Consequently it remains smooth outside the set of
valid group laws, as required for the parameter-preserving submersion theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V P I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiff_polynomialListProduct_ofFn {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => polynomialListProduct (dynkinProduct a (B p)) (List.ofFn (X p))) := by
  induction n with
  | zero => simpa [List.ofFn_zero, polynomialListProduct] using
      (contDiff_const : ContDiff ℝ k (fun _ : P => (0 : V)))
  | succ n ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact contDiff_dynkinProduct a B _ _ hB (hX 0)
      (ih (fun p i => X p i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Formal partial derivatives are the actual differential -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasFDerivAt_mvPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDifferential p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential, pderiv_C] using hasFDerivAt_const c x
  | add p q hp hq =>
      simp only [map_add]
      refine (hp.add hq).congr_fderiv ?_
      simp [polynomialDifferential, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine (hp.mul (hasFDerivAt_apply j x)).congr_fderiv ?_
      ext v
      simp [polynomialDifferential, Pi.single_apply, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, apply_ite, ite_mul, mul_assoc]

theorem polynomialDifferential_basis {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) (j : Fin m) :
    polynomialDifferential p x (Pi.single j 1) = MvPolynomial.eval x (pderiv j p) := by
  classical
  simp [polynomialDifferential, Pi.single_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMinor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial derivative minors and their uniform degree bounds -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem totalDegree_pderiv_le {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) :
    (pderiv j p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have hc : (pderiv j p).coeff s ≠ 0 := mem_support_iff.mp hs
  rw [coeff_pderiv] at hc
  have hp : s + Finsupp.single j 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := le_totalDegree hp
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)] at hd
  change (s.sum fun _ e => e) ≤ p.totalDegree - 1
  omega

theorem totalDegree_polynomialJacobianMinor_le {n k D : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) :
    (polynomialJacobianMinor p).totalDegree ≤ n * (D - 1) := by
  classical
  unfold polynomialJacobianMinor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  calc
    _ ≤ (∏ i, pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (pderiv (Fin.castAdd k i) (p (σ i))).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ n * (D - 1) := by
      calc
        _ ≤ ∑ _i : Fin n, (D - 1) := Finset.sum_le_sum (fun i _ =>
          (totalDegree_pderiv_le _ _).trans (Nat.sub_le_sub_right (hp (σ i)) 1))
        _ = _ := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialFamilies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-degree polynomial formulas in the independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

theorem hasPolynomialFormula_const {P : Type} {m : ℕ} (c : P → ℝ) :
    HasPolynomialFormula (fun a (_ : Fin m → ℝ) => c a) :=
  ⟨0, fun a => ⟨C (c a), by simp, fun _ => by simp⟩⟩

theorem hasPolynomialFormula_coordinate {P : Type} {m : ℕ} (j : Fin m) :
    HasPolynomialFormula (fun (_ : P) (x : Fin m → ℝ) => x j) :=
  ⟨1, fun _ => ⟨X j, by simp, fun _ => by simp⟩⟩

theorem HasPolynomialFormula.add {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x + g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p + q, (totalDegree_add p q).trans (max_le (by omega) (by omega)),
    fun x => by simp [he, he']⟩

theorem HasPolynomialFormula.mul {P : Type} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x * g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p * q, (totalDegree_mul p q).trans (Nat.add_le_add hp hq),
    fun x => by simp [he, he']⟩

theorem hasPolynomialFormula_sum {P I : Type} {m : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialFormula (f i)) :
    HasPolynomialFormula (fun a x => ∑ i ∈ s, f i a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPolynomialFormula_const (P := P) (m := m) (fun _ => 0)
  | @insert i s hi ih =>
      have h₁ := hf i (Finset.mem_insert_self i s)
      have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using h₁.add h₂

theorem HasPolynomialCoordinates.exists_uniform_polynomials
    {P : Type} {m n : ℕ} {f : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) :
    ∃ D : ℕ, ∃ q : P → Fin n → MvPolynomial (Fin m) ℝ,
      (∀ a i, (q a i).totalDegree ≤ D) ∧
      ∀ a x i, MvPolynomial.eval x (q a i) = f a x i := by
  classical
  choose d hd using hf
  choose q hq hvalue using (fun a i => hd i a)
  refine ⟨∑ i, d i, q, ?_, fun a x i => hvalue a i x⟩
  intro a i
  exact (hq a i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))

theorem hasPolynomialCoordinates_const {P : Type} {m n : ℕ} (v : P → Fin n → ℝ) :
    HasPolynomialCoordinates (fun a (_ : Fin m → ℝ) => v a) :=
  fun i => hasPolynomialFormula_const (fun a => v a i)

theorem HasPolynomialCoordinates.smul {P : Type} {m n : ℕ}
    {f : P → (Fin m → ℝ) → (Fin n → ℝ)} {t : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialCoordinates f) (ht : HasPolynomialFormula t) :
    HasPolynomialCoordinates (fun a x => t a x • f a x) :=
  fun i => ht.mul (hf i)

theorem bilinear_pi_expansion {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v w : Fin n → ℝ) :
    B v w = ∑ i : Fin n, ∑ j : Fin n,
      (v i * w j) • B (Pi.single i 1) (Pi.single j 1) := by
  calc
    B v w = B (∑ i, v i • Pi.single i 1) (∑ j, w j • Pi.single j 1) := by
      rw [← pi_eq_sum_univ' v, ← pi_eq_sum_univ' w]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]

theorem HasPolynomialCoordinates.bilinear {P : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun a x => B a (f a x) (g a x)) := by
  intro l
  have he : (fun a x => B a (f a x) (g a x) l) =
      (fun a x => ∑ i : Fin n, ∑ j : Fin n,
        (f a x i * g a x j) * B a (Pi.single i 1) (Pi.single j 1) l) := by
    funext a x
    rw [bilinear_pi_expansion]
    simp
  rw [he]
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact ((hf i).mul (hg j)).mul (hasPolynomialFormula_const
    (fun a => B a (Pi.single i 1) (Pi.single j 1) l))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual generator endpoint schemes have uniformly bounded degree -/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_sum {P I : Type} {m n : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → (Fin n → ℝ))
    (hf : ∀ i ∈ s, HasPolynomialCoordinates (f i)) :
    HasPolynomialCoordinates (fun a x => ∑ i ∈ s, f i a x) := by
  intro l
  simpa only [Finset.sum_apply] using hasPolynomialFormula_sum s
    (fun i a x => f i a x l) (fun i hi => hf i hi l)

theorem hasPolynomialCoordinates_evalBilinearWord
    {P I : Type} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → I → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun a x => X a x i)) (w : FreeMagma I) :
    HasPolynomialCoordinates (fun a x => evalBilinearWord (B a) (X a x) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv => exact hu.bilinear B hv

theorem hasPolynomialCoordinates_bilinearDynkin
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c l)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x => bilinearDynkinPolynomial a (B b) (X b x)) := by
  apply hasPolynomialCoordinates_sum
  intro d _
  apply hasPolynomialCoordinates_sum
  intro w _
  exact (hasPolynomialCoordinates_evalBilinearWord B X hX _).smul
    (hasPolynomialFormula_const (fun _ => a d w))

theorem hasPolynomialCoordinates_dynkinProduct
    {P : Type} {m n c : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun b x => dynkinProduct a (B b) (f b x) (g b x)) := by
  apply hasPolynomialCoordinates_bilinearDynkin a B (fun b x => ![f b x, g b x])
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem hasPolynomialCoordinates_listProduct
    {P : Type} {m n c l : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x =>
      polynomialListProduct (dynkinProduct a (B b)) (List.ofFn (X b x))) := by
  induction l with
  | zero => simpa [polynomialListProduct] using
      hasPolynomialCoordinates_const (m := m) (fun _ : P => (0 : Fin n → ℝ))
  | succ l ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact hasPolynomialCoordinates_dynkinProduct a B (hX 0)
      (ih (fun b x i => X b x i.succ) (fun i => hX i.succ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SurjectiveColumns
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A surjective differential has a fixed nonzero column minor -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

theorem exists_nonsingular_column_minor {n m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hA : Function.Surjective A) :
    ∃ j : Fin n → Fin m, Function.Injective j ∧
      (Matrix.of fun i k => A (Pi.single (j k) 1) i).det ≠ 0 := by
  classical
  let v : Fin m → (Fin n → ℝ) := fun i => A (Pi.single i 1)
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    intro y _
    obtain ⟨x, rfl⟩ := hA y
    rw [pi_eq_sum_univ' x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  let J := (linearIndepOn_empty ℝ (id : (Fin n → ℝ) → (Fin n → ℝ))).extend (empty_subset (range v))
  let b : Basis J ℝ (Fin n → ℝ) := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using (finrank_eq_card_basis b).symm)
  let b' := b.reindex e
  have hb (k : Fin n) : ∃ i, v i = b' k := by
    simpa only [b', Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ range b from ⟨_, rfl⟩))
  choose j hj using hb
  refine ⟨j, ?_, ?_⟩
  · intro x y hxy
    apply b'.injective
    rw [← hj x, ← hj y, hxy]
  · have he : (Matrix.of fun i k => A (Pi.single (j k) 1) i) =
        LinearMap.toMatrix' b'.equivFun.symm.toLinearMap := by
      ext i k
      rw [LinearMap.toMatrix'_apply]
      change A (Pi.single (j k) 1) i = b'.equivFun.symm (Pi.single k 1) i
      have hs : b'.equivFun.symm (Pi.single k 1) = b' k := by
        apply b'.equivFun.injective
        simp
      rw [hs]
      exact congrFun (hj k) i
    rw [he, LinearMap.det_toMatrix']
    exact b'.equivFun.symm.isUnit_det'.ne_zero

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingProductSubmersion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Submersion of an alternating product from two linear images

If generators in the union of two images bracket-generate the limiting
algebra, one fixed alternating product has a surjective differential.
Identity factors pad the unused side of each generator slot. The rank is
proved for the full product map, before restricting any parameters.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {U V : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_alternatingCoordinateProduct {c h : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (L₁ L₂ : U →L[ℝ] V) :
    ContDiff ℝ q (alternatingCoordinateProduct (h := h) a B L₁ L₂) := by
  apply contDiff_polynomialListProduct_ofFn a (fun _ => B) _ contDiff_const
  intro j
  apply contDiff_dynkinProduct a (fun _ => B) _ _ contDiff_const
  · exact L₁.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ (U × U) j))
  · exact L₂.contDiff.comp (contDiff_snd.comp (contDiff_apply ℝ (U × U) j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingPolynomialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and smooth coordinates for the alternating product

These coordinates keep the two embedding maps among the coefficient
parameters. The input chart can be any fixed continuous linear equivalence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_linear {P : Type} {m n : ℕ}
    (L : P → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    HasPolynomialCoordinates (fun p x => L p x) := by
  have he (p : P) (x : Fin m → ℝ) :
      L p x = ∑ i, x i • L p (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  intro j
  have hj : (fun p x => L p x j) =
      (fun p x => ∑ i, x i * L p (Pi.single i 1) j) := by
    funext p x
    rw [he p x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hj]
  apply hasPolynomialFormula_sum
  intro i _
  exact (hasPolynomialFormula_coordinate i).mul
    (hasPolynomialFormula_const (fun p => L p (Pi.single i 1) j))

theorem hasPolynomialCoordinates_flatAlternatingProduct {m n h c : ℕ}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ))) :
    HasPolynomialCoordinates (flatAlternatingProduct a e) := by
  unfold flatAlternatingProduct alternatingCoordinateProduct
  apply hasPolynomialCoordinates_listProduct a (fun p : AlternatingLawData n => p.1)
  intro j
  apply hasPolynomialCoordinates_dynkinProduct a (fun p : AlternatingLawData n => p.1)
  · exact hasPolynomialCoordinates_linear (fun p : AlternatingLawData n =>
      p.2.1.comp ((ContinuousLinearMap.fst ℝ _ _).comp
        ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)))
  · exact hasPolynomialCoordinates_linear (fun p : AlternatingLawData n =>
      p.2.2.comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)))

theorem contDiff_flatAlternatingProduct {m n h c : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ))) :
    ContDiff ℝ q (fun z : AlternatingLawData n × (Fin m → ℝ) =>
      flatAlternatingProduct a e z.1 z.2) := by
  unfold flatAlternatingProduct alternatingCoordinateProduct
  apply contDiff_polynomialListProduct_ofFn a
    (fun z : AlternatingLawData n × (Fin m → ℝ) => z.1.1) _ contDiff_fst.fst
  intro j
  apply contDiff_dynkinProduct a
    (fun z : AlternatingLawData n × (Fin m → ℝ) => z.1.1) _ _ contDiff_fst.fst
  · exact contDiff_fst.snd.fst.clm_apply
      (((contDiff_apply ℝ ((Fin n → ℝ) × (Fin n → ℝ)) j).comp
        (e.contDiff.comp contDiff_snd)).fst)
  · exact contDiff_fst.snd.snd.clm_apply
      (((contDiff_apply ℝ ((Fin n → ℝ) × (Fin n → ℝ)) j).comp
        (e.contDiff.comp contDiff_snd)).snd)

theorem flatAlternatingProduct_submersive {m n h c : ℕ}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (p : AlternatingLawData n) (z : Fin h → (Fin n → ℝ) × (Fin n → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p.1 p.2.1 p.2.2) z)) :
    Function.Surjective (fderiv ℝ (flatAlternatingProduct a e p) (e.symm z)) := by
  have hf : DifferentiableAt ℝ (alternatingCoordinateProduct a p.1 p.2.1 p.2.2)
      (e (e.symm z)) :=
    ((contDiff_alternatingCoordinateProduct (q := 1) a p.1 p.2.1 p.2.2).differentiable
      one_ne_zero) _
  have hd := hf.hasFDerivAt.comp (e.symm z) e.hasFDerivAt
  rw [e.apply_symm_apply] at hd
  change HasFDerivAt (flatAlternatingProduct a e p) _ (e.symm z) at hd
  intro y
  obtain ⟨v, hv⟩ := hs y
  refine ⟨e.symm v, ?_⟩
  rw [hd.fderiv]
  simpa using hv

end PolycyclicRecognition

end

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

theorem HasSubexponentialLowerBoundSeq.eventually_pos {scale f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) : ∀ᶠ n in atTop, 0 < f n :=
  (hf 1 zero_lt_one).mono (fun _ h => (Real.exp_pos _).trans_le h)

theorem HasSubexponentialLowerBoundSeq.mono {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hfg : f ≤ᶠ[atTop] g) :
    HasSubexponentialLowerBoundSeq scale g := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with n hn hfg
  exact hn.trans hfg

theorem HasSubexponentialLowerBoundSeq.mul {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) *
        Real.exp (-(ε / 2) * scale n) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ f n * g n := mul_le_mul hn hm (Real.exp_pos _).le ((Real.exp_pos _).trans_le hn).le

theorem HasSubexponentialLowerBoundSeq.div {scale f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hg0 : ∀ᶠ n in atTop, 0 < g n) :
    HasSubexponentialLowerBoundSeq scale (fun n => f n / g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hg0] with n hn hm h0
  calc
    Real.exp (-ε * scale n) = Real.exp (-(ε / 2) * scale n) /
        Real.exp (ε / 2 * scale n) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ f n / g n := div_le_div₀ ((Real.exp_pos _).trans_le hn).le hn h0 hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GrowingPositiveParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive parameter sets on growing input cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_positive_parameter_sets_growing_sequence {m : ℕ} (R : ℕ → ℝ)
    (scale : ℕ → ℝ) (hR : ∀ r, 0 < R r)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ F : ℕ → Set (Fin m → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 (R r)) ∧
      (∀ r, 0 < (volume (F r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ᶠ r in atTop, F r = E r := by
  classical
  let F := fun r => if 0 < (volume (E r)).toReal then E r else closedBall 0 (R r)
  have heq : ∀ᶠ r in atTop, F r = E r :=
    hmlower.eventually_pos.mono (fun _ h => ite_eq_left h)
  have hball (r : ℕ) : 0 < (volume (closedBall (0 : Fin m → ℝ) (R r))).toReal := by
    have hr := hR r
    rw [Real.volume_pi_closedBall _ (hR r).le, ENNReal.toReal_ofReal (by positivity)]
    positivity
  refine ⟨F, ?_, ?_, ?_, ?_, heq⟩
  · intro r
    dsimp [F]
    split_ifs
    · exact hE r
    · exact measurableSet_closedBall
  · intro r
    dsimp [F]
    split_ifs
    · exact hER r
    · exact Subset.rfl
  · intro r
    dsimp [F]
    split_ifs with h
    · exact h
    · exact hball r
  · apply hmlower.mono
    exact heq.mono (fun _ h => le_of_eq (congrArg (fun s => (volume s).toReal) h.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParameterSplit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the independent parameter cube preserves volume -/

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin k => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + k) => ℝ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
      change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
      simp
  | inr j =>
      change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
      simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialMinorDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

theorem appendParameterLinear_apply (n k : ℕ) (v : Fin n → ℝ) :
    appendParameterLinear n k v = Fin.append v 0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [appendParameterLinear]

theorem hasFDerivAt_finAppend {n k : ℕ} (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w => Fin.append w z) (appendParameterLinear n k) v := by
  convert (appendParameterLinear n k).hasFDerivAt.add_const (Fin.append 0 z) using 1
  all_goals try with_reducible_and_instances rfl
  ext w i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [appendParameterLinear_apply]

theorem hasFDerivAt_polynomialSlice {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w i => MvPolynomial.eval (Fin.append w z) (p i))
      (polynomialSliceDifferential p v z) v := by
  exact (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mvPolynomial_eval (p i) (Fin.append v z))).comp v
    (hasFDerivAt_finAppend v z)

theorem eval_polynomialJacobianMinor {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor p) =
      (polynomialSliceDifferential p v z).det := by
  classical
  rw [polynomialJacobianMinor, RingHom.map_det]
  change _ = (polynomialSliceDifferential p v z).toLinearMap.det
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change MvPolynomial.eval (Fin.append v z) (pderiv (Fin.castAdd k j) (p i)) =
    polynomialDifferential (p i) (Fin.append v z) (appendParameterLinear n k (Pi.single j 1))
  have he : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    rw [appendParameterLinear_apply]
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [he, polynomialDifferential_basis]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMinorPermutation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering an actual nonzero minor into the sliced coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

theorem exists_fin_equiv_extending_injection {n m : ℕ}
    (j : Fin n → Fin m) (hj : Function.Injective j) :
    ∃ k : ℕ, ∃ e : Fin (n + k) ≃ Fin m, ∀ i, e (Fin.castAdd k i) = j i := by
  classical
  let s : Set (Fin m) := range j
  let k := Fintype.card ↥(sᶜ)
  let ec : ↥(sᶜ) ≃ Fin k := Fintype.equivFin _
  let e : Fin (n + k) ≃ Fin m := finSumFinEquiv.symm.trans
    (((Equiv.ofInjective j hj).sumCongr ec.symm).trans (Equiv.Set.sumCompl (range j)))
  refine ⟨k, e, fun i => ?_⟩
  simp [e]

theorem reindexParameters_norm {l m : ℕ} (e : Fin l ≃ Fin m) (x : Fin l → ℝ) :
    ‖reindexParameters e x‖ = ‖x‖ := by
  have h := (IsometryEquiv.piCongrLeft' (Y := fun _ : Fin l => ℝ) e).isometry.dist_eq x 0
  change dist (reindexParameters e x) (reindexParameters e 0) = dist x 0 at h
  simpa only [map_zero, dist_zero_right] using h

theorem measurePreserving_reindexParameters {l m : ℕ} (e : Fin l ≃ Fin m) :
    MeasurePreserving (reindexParameters e) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) e using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, reindexParameters_apply_equiv]

theorem HasPolynomialFormula.reindex {P : Type} {l m : ℕ}
    {f : P → (Fin m → ℝ) → ℝ} (hf : HasPolynomialFormula f) (e : Fin l ≃ Fin m) :
    HasPolynomialFormula (fun a x => f a (reindexParameters e x)) := by
  obtain ⟨D, hD⟩ := hf
  refine ⟨D, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  refine ⟨MvPolynomial.rename e.symm p, (MvPolynomial.totalDegree_rename_le _ _).trans hp, ?_⟩
  intro x
  rw [MvPolynomial.eval_rename]
  exact he _

theorem reindexParameters_single {l m : ℕ} (e : Fin l ≃ Fin m) (j : Fin l) :
    reindexParameters e (Pi.single j 1) = Pi.single (e j) 1 := by
  classical
  ext i
  obtain ⟨i, rfl⟩ := e.surjective i
  simp [Pi.single_apply, e.injective.eq_iff]

/-- The selected column determinant is the derivative determinant after reordering. -/
theorem det_reindexed_slice {n k m : ℕ} (e : Fin (n + k) ≃ Fin m)
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (v : Fin n → ℝ) (z : Fin k → ℝ)
    (hf : DifferentiableAt ℝ f (reindexParameters e (Fin.append v z))) :
    (fderiv ℝ (fun w => f (reindexParameters e (Fin.append w z))) v).det =
      (Matrix.of fun i j => fderiv ℝ f (reindexParameters e (Fin.append v z))
        (Pi.single (e (Fin.castAdd k j)) 1) i).det := by
  have hd := hf.hasFDerivAt.comp v
    ((reindexParameters e).hasFDerivAt.comp v (hasFDerivAt_finAppend v z))
  change HasFDerivAt (fun w => f (reindexParameters e (Fin.append w z))) _ v at hd
  rw [hd.fderiv]
  change (ContinuousLinearMap.comp _ _).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ f _ (reindexParameters e (appendParameterLinear n k (Pi.single j 1))) i = _
  have ha : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [appendParameterLinear, Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [ha, reindexParameters_single]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialLargeValueSet
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping compact parameter mass away from a polynomial zero set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem exists_compact_large_polynomial_values
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
      ∀ (R c : ℝ), 1 ≤ R → 0 < c →
      ∀ x₀ ∈ closedBall 0 R, c ≤ |MvPolynomial.eval x₀ p| →
      ∀ E : Set (Fin n → ℝ), MeasurableSet E → E ⊆ closedBall 0 R →
      0 < (volume E).toReal →
      let η := (c / 2) / (2 * A * (1 + R) ^ n / (volume E).toReal) ^ (n * D)
      ∃ K : Set (Fin n → ℝ), K ⊆ E ∧ IsCompact K ∧
        (volume E).toReal / 4 < (volume K).toReal ∧
        ∀ x ∈ K, η ≤ |MvPolynomial.eval x p| := by
  obtain ⟨A, hA, hrem⟩ := rem n D hn hD
  refine ⟨A, hA, ?_⟩
  intro p hp R c hR hc x₀ hx₀ hx₀c E hE hER hm
  let m := (volume E).toReal
  let a := 2 * A * (1 + R) ^ n / m
  let η := (c / 2) / a ^ (n * D)
  have ha : 0 < a := by dsimp [a, m] <;> positivity
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hEfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hER (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
  let B := E ∩ {x | |MvPolynomial.eval x p| < η}
  let G := E ∩ {x | η ≤ |MvPolynomial.eval x p|}
  have hB : MeasurableSet B := hE.inter
    (isOpen_lt p.continuous_eval.abs continuous_const).measurableSet
  have hG : MeasurableSet G := hE.inter
    (isClosed_le continuous_const p.continuous_eval.abs).measurableSet
  have hBfinite : volume B ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hGfinite : volume G ≠ ∞ := measure_ne_top_of_subset inter_subset_left hEfinite
  have hBmass : (volume B).toReal ≤ m / 2 := by
    by_contra h
    have hlarge : m / 2 < (volume B).toReal := lt_of_not_ge h
    have hBpos : 0 < (volume B).toReal := (by dsimp [m]; positivity : 0 < m / 2).trans hlarge
    have hpoint := hrem p hp R hR B hB (inter_subset_left.trans hER) hBpos
      η hη.le (fun x hx => hx.2.le) x₀ hx₀
    have hquot : A * (1 + R) ^ n / (volume B).toReal ≤ a := by
      dsimp [a]
      apply (div_le_div_iff₀ hBpos hm).mpr
      have hnonneg : 0 ≤ A * (1 + R) ^ n := by positivity
      nlinarith
    have hpow : (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) ≤ a ^ (n * D) :=
      pow_le_pow_left₀ (by positivity) hquot (n * D)
    have he : a ^ (n * D) * η = c / 2 := by
      dsimp [η]
      field_simp
    have hlast : c ≤ c / 2 := calc
      c ≤ |MvPolynomial.eval x₀ p| := hx₀c
      _ ≤ (A * (1 + R) ^ n / (volume B).toReal) ^ (n * D) * η := hpoint
      _ ≤ a ^ (n * D) * η := mul_le_mul_of_nonneg_right hpow hη.le
      _ = c / 2 := he
    linarith
  have hEG : E = B ∪ G := by
    ext x
    simp only [B, G, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      rcases lt_or_ge |MvPolynomial.eval x p| η with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hGmass : m / 2 ≤ (volume G).toReal := by
    have hu := measureReal_union_le (μ := volume) B G
    rw [← hEG] at hu
    change m ≤ (volume B).toReal + (volume G).toReal at hu
    linarith
  have hstrict : ENNReal.ofReal (m / 4) < volume G := by
    apply (ENNReal.toReal_lt_toReal (by simp) hGfinite).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  obtain ⟨K, hKG, hK, hKmass⟩ := hG.exists_lt_isCompact hstrict
  refine ⟨K, hKG.trans inter_subset_left, hK, ?_, fun x hx => (hKG hx).2⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hK.measure_ne_top).mpr hKmass
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ m / 4)] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining parameter volume on one coordinate slice -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Fubini gives a large section without choosing a measurable family of
representatives for the image of the parameter set. -/
theorem exists_section_measure_gt
    {V Z : Type} [MeasurableSpace V] [MeasurableSpace Z]
    (μ : Measure V) (ν : Measure Z) [SFinite μ] [SFinite ν]
    {K : Set (V × Z)} (hK : MeasurableSet K)
    {Q : Set Z} (hQ : MeasurableSet Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q) (t : ℝ≥0∞)
    (hmass : t * ν Q < (μ.prod ν) K) :
    ∃ z ∈ Q, t < μ {v | (v, z) ∈ K} := by
  by_contra h
  have hbound (z : Z) : μ {v | (v, z) ∈ K} ≤ Q.indicator (fun _ => t) z := by
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz]
      exact le_of_not_gt (fun ht => h ⟨z, hz, ht⟩)
    · have hempty : {v | (v, z) ∈ K} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hz (hKQ (v, z) hv)
      rw [hempty, measure_empty, indicator_of_notMem hz]
  have he : (μ.prod ν) K ≤ t * ν Q := by
    rw [Measure.prod_apply_symm hK]
    calc
      _ ≤ ∫⁻ z, Q.indicator (fun _ => t) z ∂ν := lintegral_mono hbound
      _ = t * ν Q := by rw [lintegral_indicator hQ]; simp
  exact not_lt_of_ge he hmass

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSectionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact coordinate sections with quantitative retained volume -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

theorem isCompact_coordinate_section
    {V Z : Type} [TopologicalSpace V] [TopologicalSpace Z] [T1Space Z]
    {K : Set (V × Z)} (hK : IsCompact K) (z : Z) :
    IsCompact {v | (v, z) ∈ K} := by
  have he : {v | (v, z) ∈ K} =
      Prod.fst '' (K ∩ Prod.snd ⁻¹' {z}) := by
    ext v
    constructor
    · intro hv
      exact ⟨(v, z), ⟨hv, rfl⟩, rfl⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hy
      change (w, z) ∈ K
      simpa only [hy] using hw
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem exists_compact_section_volume_gt
    (n k : ℕ) {K : Set ((Fin n → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) {Q : Set (Fin k → ℝ)} (hQ : IsCompact Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q)
    {t q : ℝ} (ht : 0 ≤ t) (hq : (volume Q).toReal ≤ q)
    (hmass : t * q < (volume K).toReal) :
    ∃ z ∈ Q, IsCompact {v | (v, z) ∈ K} ∧
      t < (volume {v | (v, z) ∈ K}).toReal := by
  have hlt : ENNReal.ofReal t * volume Q < volume K := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by simp) hQ.measure_ne_top) hK.measure_ne_top).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    exact (mul_le_mul_of_nonneg_left hq ht).trans_lt hmass
  obtain ⟨z, hz, hvolume⟩ := exists_section_measure_gt volume volume hK.measurableSet
    hQ.measurableSet hKQ (ENNReal.ofReal t) hlt
  have hsection := isCompact_coordinate_section hK z
  refine ⟨z, hz, hsection, ?_⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hsection.measure_ne_top).mpr hvolume
  simpa only [ENNReal.toReal_ofReal ht] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InjectivePatchVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume lower bounds from a controlled finite injective cover

This is the change-of-variables step for measurable polynomial parameters.
The parameter set itself need not contain an open set. When it is compact,
the image used below is a compact witness for inner volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem volume_image_lower_of_finite_injective_cover
    {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : V → V) (df : V → V →L[ℝ] V)
    {K : Set V} (hK : MeasurableSet K) (s : Finset I) (U : I → Set V)
    (hU : ∀ i ∈ s, MeasurableSet (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i)
    (hdf : ∀ x ∈ K, HasFDerivAt f (df x) x)
    (hinj : ∀ i ∈ s, Set.InjOn f (K ∩ U i))
    (η : ℝ≥0) (hdet : ∀ x ∈ K, (η : ℝ) ≤ |(df x).det|) :
    (η : ℝ≥0∞) * μ K ≤ (s.card : ℝ≥0∞) * μ (f '' K) := by
  classical
  have hcover' : K ⊆ ⋃ i ∈ s, K ∩ U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  have hmass : μ K ≤ ∑ i ∈ s, μ (K ∩ U i) :=
    (measure_mono hcover').trans (measure_biUnion_finset_le s (fun i => K ∩ U i))
  calc
    (η : ℝ≥0∞) * μ K ≤ η * ∑ i ∈ s, μ (K ∩ U i) := mul_le_mul' le_rfl hmass
    _ = ∑ i ∈ s, (η : ℝ≥0∞) * μ (K ∩ U i) := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ s, μ (f '' K) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (η : ℝ≥0∞) * μ (K ∩ U i) = ∫⁻ _x in K ∩ U i, (η : ℝ≥0∞) ∂μ := by simp
        _ ≤ ∫⁻ x in K ∩ U i, ENNReal.ofReal |(df x).det| ∂μ := by
          apply setLIntegral_mono' (hK.inter (hU i hi))
          intro x hx
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (hdet x hx.1)
        _ = μ (f '' (K ∩ U i)) :=
          lintegral_abs_det_fderiv_eq_addHaar_image μ (hK.inter (hU i hi))
            (fun x hx => (hdf x hx.1).hasFDerivWithinAt) (hinj i hi)
        _ ≤ μ (f '' K) := measure_mono (image_mono inter_subset_left)
    _ = (s.card : ℝ≥0∞) * μ (f '' K) := by simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial-size coordinate mesh for a bounded parameter cube -/

noncomputable section

namespace PolycyclicRecognition

theorem exists_coordinate_mesh (n : ℕ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * R / ρ + 2 ∧
      ∃ c : (Fin n → Fin k) → (Fin n → ℝ),
        (∀ i, ‖c i‖ ≤ R + ρ) ∧
        ∀ x : Fin n → ℝ, ‖x‖ ≤ R → ∃ i, dist x (c i) ≤ ρ := by
  let k := ⌈2 * R / ρ⌉₊ + 1
  have hratio : 0 ≤ 2 * R / ρ := div_nonneg (by positivity) hρ.le
  have hk : (k : ℝ) ≤ 2 * R / ρ + 2 := by
    dsimp only [k]
    have h := Nat.ceil_lt_add_one hratio
    push_cast
    linarith
  let c := fun i : Fin n → Fin k => fun j => -R + ρ * (i j : ℕ)
  refine ⟨k, hk, c, ?_, ?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R + ρ)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have hji : (i j : ℕ) ≤ ⌈2 * R / ρ⌉₊ := Nat.le_of_lt_succ (i j).isLt
    have hj : ((i j : ℕ) : ℝ) ≤ (⌈2 * R / ρ⌉₊ : ℝ) := by exact_mod_cast hji
    have hc := Nat.ceil_lt_add_one hratio
    have hp : ρ * ((i j : ℕ) : ℝ) ≤ 2 * R + ρ := by
      have ht := mul_le_mul_of_nonneg_left (hj.trans hc.le) hρ.le
      have he : ρ * (2 * R / ρ + 1) = 2 * R + ρ := by field_simp
      rwa [he] at ht
    dsimp only [c]
    constructor
    · nlinarith [show (0 : ℝ) ≤ ((i j : ℕ) : ℝ) from Nat.cast_nonneg _]
    · linarith
  · intro x hx
    have hxj := (pi_norm_le_iff_of_nonneg hR).mp hx
    let i : Fin n → Fin k := fun j => ⟨⌊(x j + R) / ρ⌋₊, by
      have hj : (x j + R) / ρ ≤ 2 * R / ρ := by
        apply div_le_div_of_nonneg_right _ hρ.le
        have := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).2
        linarith
      exact Nat.lt_succ_of_le ((Nat.floor_mono hj).trans (Nat.floor_le_ceil _))⟩
    refine ⟨i, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
    intro j
    have hlow : -R ≤ x j := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hxj j)).1
    have hnonneg : 0 ≤ (x j + R) / ρ := div_nonneg (by linarith) hρ.le
    have hlo := (le_div_iff₀ hρ).mp (Nat.floor_le hnonneg)
    have hhi := (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one ((x j + R) / ρ))
    change ‖x j - (-R + ρ * (⌊(x j + R) / ρ⌋₊ : ℝ))‖ ≤ ρ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DeterminantLowerNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative invertibility from a determinant lower bound

Compactness bounds the adjugate on the unit ball. Homogeneity then gives
the polynomial loss needed to choose injective patches for polynomial maps.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric Matrix
open scoped Matrix.Norms.Operator

theorem exists_adjugate_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin n) (Fin n) ℝ) (L : ℝ),
      0 < L → ‖A‖ ≤ L → ‖A.adjugate‖ ≤ C * L ^ (n - 1) := by
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) :=
    continuous_id.matrix_adjugate
  obtain ⟨C, hC, hbound⟩ := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1).image hc
    |>.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun A L hL hA => ?_⟩
  have hunit : L⁻¹ • A ∈ closedBall (0 : Matrix (Fin n) (Fin n) ℝ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact (inv_mul_le_iff₀ hL).mpr (by simpa using hA)
  have h := hbound _ ⟨L⁻¹ • A, hunit, rfl⟩
  dsimp only at h
  rw [Matrix.adjugate_smul, Fintype.card_fin, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (inv_pos.mpr hL) _), inv_pow] at h
  have he := (inv_mul_le_iff₀ (pow_pos hL (n - 1))).mp h
  simpa only [mul_comm] using he

/-- The adjugate identity bounds below the action of the original matrix. -/
theorem determinant_mul_norm_le_adjugate_mul_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    |A.det| * ‖v‖ ≤ ‖A.adjugate‖ * ‖A *ᵥ v‖ := by
  have he : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hb := Matrix.linfty_opNorm_mulVec A.adjugate (A *ᵥ v)
  rw [he, norm_smul, Real.norm_eq_abs] at hb
  exact hb

/-- Uniform lower norm control for all matrices with bounded norm and a
prescribed positive determinant lower bound. -/
theorem exists_determinant_lower_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (L η : ℝ),
      0 < L → ‖A‖ ≤ L → η ≤ |A.det| → ∀ v,
      η * ‖v‖ ≤ (C * L ^ (n - 1)) * ‖A v‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_adjugate_norm_bound n
  refine ⟨C, hC, fun A L η hL hA hη v => ?_⟩
  let M := LinearMap.toMatrix' A.toLinearMap
  have hM : ‖M‖ ≤ L := by simpa only [M, Matrix.linfty_opNorm_toMatrix] using hA
  have hb := determinant_mul_norm_le_adjugate_mul_norm M v
  dsimp only [M] at hb
  rw [LinearMap.det_toMatrix', LinearMap.toMatrix'_mulVec] at hb
  exact (mul_le_mul_of_nonneg_right hη (norm_nonneg v)).trans
    (hb.trans (mul_le_mul_of_nonneg_right (hbound M L hL hM) (norm_nonneg (A v))))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivativeOscillation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectivity on convex patches with controlled derivative oscillation -/

namespace PolycyclicRecognition

open Set

theorem injOn_of_derivative_oscillation
    {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (df : V → V →L[ℝ] W) (A : V →L[ℝ] W)
    {S : Set V} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, HasFDerivAt f (df x) x)
    {η D ε : ℝ} (hD : 0 ≤ D) (hgap : D * ε < η)
    (hA : ∀ v, η * ‖v‖ ≤ D * ‖A v‖)
    (hosc : ∀ x ∈ S, ‖df x - A‖ ≤ ε) : Set.InjOn f S := by
  intro x hx y hy hxy
  have he := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - A z) (f' := fun z => df z - A)
    (fun z hz => ((hf z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hosc hx hy
  have hn : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    rw [map_sub, norm_sub_rev]
    simpa only [hxy, sub_sub_sub_cancel_left] using he
  have hb := (hA (y - x)).trans (mul_le_mul_of_nonneg_left hn hD)
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_QuantitativeInjectiveCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative injective patches near nondegenerate derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem exists_quantitative_injective_cover (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∃ (ρ : ℝ) (k : ℕ) (c : (Fin n → Fin k) → (Fin n → ℝ)),
        ρ = min 1 (η / (8 * (C * L ^ (n - 1)) * L)) ∧ 0 < ρ ∧
        (k : ℝ) ≤ 2 * R / ρ + 2 ∧
        (∀ z, ‖z‖ ≤ R → ∃ i, z ∈ closedBall (c i) ρ) ∧
        ∀ i, Set.InjOn f
          ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ) := by
  obtain ⟨C, hC, hbound⟩ := exists_determinant_lower_norm_bound n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let D := C * L ^ (n - 1)
  have hD : 0 < D := mul_pos hC (pow_pos hLpos _)
  let ρ := min 1 (η / (8 * D * L))
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hη (by positivity))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hgap : D * (2 * L * ρ) < η := by
    have hρle : ρ ≤ η / (8 * D * L) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 8 * D * L by positivity)).mp hρle
    nlinarith
  obtain ⟨k, hk, c, hc, hcover⟩ := exists_coordinate_mesh n hR hρ
  refine ⟨ρ, k, c, rfl, hρ, hk, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, hi⟩
  · intro i
    by_cases hempty : ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ).Nonempty
    · obtain ⟨z₀, hz₀, hz₀ball⟩ := hempty
      have hbig (z : Fin n → ℝ) (hz : z ∈ closedBall (c i) ρ) : ‖z‖ ≤ R + 2 := by
        have he : ‖z‖ ≤ ‖z - c i‖ + ‖c i‖ := by
          simpa only [dist_eq_norm, sub_zero] using dist_triangle z (c i) 0
        have hd : ‖z - c i‖ ≤ ρ := hz
        have hh := hc i
        linarith
      have hi : Set.InjOn f (closedBall (c i) ρ) := by
        apply injOn_of_derivative_oscillation f df (df z₀) (convex_closedBall _ _)
          (fun z hz => hf z (hbig z hz)) hD.le hgap
        · exact hbound (df z₀) L η hLpos (hdf z₀ (hbig z₀ hz₀ball)) hz₀.2
        · intro z hz
          have hd : dist z z₀ ≤ 2 * ρ := by
            calc
              dist z z₀ ≤ dist z (c i) + dist (c i) z₀ := dist_triangle _ _ _
              _ ≤ ρ + ρ := add_le_add hz
                (by simpa only [dist_comm] using (mem_closedBall.mp hz₀ball))
              _ = 2 * ρ := by ring
          exact (hosc z z₀ (hbig z hz) (hbig z₀ hz₀ball)).trans
            (by nlinarith [mul_le_mul_of_nonneg_left hd hLpos.le])
      exact hi.mono inter_subset_right
    · simpa only [not_nonempty_iff_eq_empty.mp hempty] using (Set.injOn_empty f)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactImageVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative compact image volume away from the critical set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_compact_image_volume_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∀ K : Set (Fin n → ℝ), IsCompact K →
      (∀ z ∈ K, ‖z‖ ≤ R ∧ η ≤ |(df z).det|) →
      let ρ := min 1 (η / (8 * (C * L ^ (n - 1)) * L))
      IsCompact (f '' K) ∧
        η * (volume K).toReal ≤ (2 * R / ρ + 2) ^ n * (volume (f '' K)).toReal := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_quantitative_injective_cover n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc K hK hgood
  obtain ⟨ρ, k, c, hρeq, hρ, hk, hcov, hinj⟩ := hcover f df R L η hR hL hη hf hdf hosc
  have hcont : ContinuousOn f K := fun z hz =>
    (hf z (by have := (hgood z hz).1; linarith)).continuousAt.continuousWithinAt
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hcont
  have hinjK (i : Fin n → Fin k) : Set.InjOn f (K ∩ closedBall (c i) ρ) := by
    intro z hz w hw he
    exact hinj i ⟨hgood z hz.1, hz.2⟩ ⟨hgood w hw.1, hw.2⟩ he
  have hb := volume_image_lower_of_finite_injective_cover volume f df hK.measurableSet
    (Finset.univ : Finset (Fin n → Fin k)) (fun i => closedBall (c i) ρ)
    (fun _ _ => measurableSet_closedBall) (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z (hgood z hz).1
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)
    (fun z hz => hf z (by have := (hgood z hz).1; linarith))
    (fun i _ => hinjK i)
    (Real.toNNReal η) (fun z hz => by simpa [Real.coe_toNNReal η hη.le] using (hgood z hz).2)
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) himage.measure_ne_top) hb
  have hr : η * (volume K).toReal ≤ (k : ℝ) ^ n * (volume (f '' K)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal η hη.le,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, Nat.cast_pow] using ht
  have hpow : (k : ℝ) ^ n ≤ (2 * R / ρ + 2) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) hk n
  subst ρ
  exact ⟨himage, hr.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialFamilyImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable images in a compact smooth polynomial family

Smoothness supplies all local differential bounds. The polynomial formulas
supply the actual minor and its fixed degree. Only scalar Remez is external.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory

theorem contDiff_finAppend (n k : ℕ) {q : ℕ∞} :
    ContDiff ℝ q (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simpa only [Fin.append_left, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_fst (E := Fin n → ℝ) (F := Fin k → ℝ))
  · simpa only [Fin.append_right, Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp (contDiff_snd (E := Fin n → ℝ) (F := Fin k → ℝ))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A noncritical limit supplies the minor bound for all late parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem continuous_det_clm {P : Type} [TopologicalSpace P] {n : ℕ}
    {d : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hd : Continuous d) :
    Continuous (fun p => (d p).det) := by
  have hm : Continuous (fun p => LinearMap.toMatrix' (d p).toLinearMap) := by
    apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (hd.clm_apply continuous_const)
  simpa only [LinearMap.det_toMatrix'] using hm.matrix_det

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoefficientContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a continuous bounded-degree polynomial family

Each coefficient is a fixed finite linear combination of evaluations on
the finite-dimensional space of bounded-degree polynomials. This supplies
uniform coefficient bounds from compact parameter sets, even when the
input cubes have growing radii.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MvPolynomial

theorem boundedDegreeCoefficient_mem_span_evaluations {m : ℕ}
    (D : ℕ) (s : Fin m →₀ ℕ) :
    (lcoeff ℝ s).comp (restrictTotalDegree (Fin m) ℝ D).subtype ∈
      Submodule.span ℝ (Set.range (boundedDegreeEvaluation (m := m) D)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro p hp
  have he (x : Fin m → ℝ) : eval x p.val = 0 := by
    have hx := (Submodule.mem_iInf _).mp hp x
    exact hx
  have hz : p.val = 0 := MvPolynomial.funext (fun x => by simpa using he x)
  change p.val.coeff s = 0
  rw [hz]
  rfl

theorem continuous_polynomial_coefficients {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (s : Fin m →₀ ℕ) : Continuous (fun a => (p a).coeff s) := by
  classical
  obtain ⟨t, ht⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (boundedDegreeCoefficient_mem_span_evaluations D s)
  have hrep (a : P) : (p a).coeff s =
      ∑ x ∈ t.support, t x * eval x (p a) := by
    have hp : p a ∈ restrictTotalDegree (Fin m) ℝ D :=
      (mem_restrictTotalDegree _ _ _).mpr (hD a)
    have h := congrArg (fun L : restrictTotalDegree (Fin m) ℝ D →ₗ[ℝ] ℝ => L ⟨p a, hp⟩) ht
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, boundedDegreeEvaluation] using h.symm
  simp_rw [hrep]
  apply continuous_finsetSum
  intro x _
  exact continuous_const.mul (heval x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformPolynomialGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform polynomial growth over compact coefficient families -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set
open scoped BigOperators

theorem norm_monomial_value_le {m D : ℕ} (s : Fin m →₀ ℕ)
    (hs : ∀ i, s i ≤ D) (x : Fin m → ℝ) :
    |∏ i, x i ^ s i| ≤ (1 + ‖x‖) ^ (m * D) := by
  rw [Finset.abs_prod]
  calc
    ∏ i, |x i ^ s i| ≤ ∏ _i : Fin m, (1 + ‖x‖) ^ D := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm x i).trans
        (by linarith [norm_nonneg x])) _).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (hs i))
    _ = (1 + ‖x‖) ^ (m * D) := by simp [← pow_mul, Nat.mul_comm]

theorem polynomial_support_subset_bounded_exponents {m D : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ D) :
    p.support ⊆ (finite_bounded_exponents m D).toFinset := by
  intro s hs
  simp only [Finite.mem_toFinset]
  intro i
  exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans hp

theorem continuous_polynomial_evaluation_of_coefficients
    {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (hc : ∀ s, Continuous (fun a => (p a).coeff s)) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (p a)) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have he (a : P) : eval x (p a) = ∑ s ∈ T, (p a).coeff s * ∏ i, x i ^ s i := by
    rw [eval_eq']
    apply Finset.sum_subset (polynomial_support_subset_bounded_exponents (p a) (hD a))
    intro s _ hs
    have hz : (p a).coeff s = 0 := notMem_support_iff.mp hs
    rw [hz, zero_mul]
  simp_rw [he]
  exact continuous_finsetSum _ (fun s _ => (hc s).mul continuous_const)

theorem exists_uniform_polynomial_growth
    {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ x : Fin m → ℝ,
      |eval x (p a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have hb (s : Fin m →₀ ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ S, |(p a).coeff s| ≤ B := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (continuous_polynomial_coefficients p D hD heval s).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun a ha => (hB a ha).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let C := max 1 (∑ s ∈ T, B s)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha x
  have hsub : (p a).support ⊆ T :=
    polynomial_support_subset_bounded_exponents (p a) (hD a)
  rw [eval_eq']
  calc
    |∑ s ∈ (p a).support, (p a).coeff s * ∏ i, x i ^ s i| ≤
        ∑ s ∈ (p a).support, |(p a).coeff s * ∏ i, x i ^ s i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (p a).support, B s * (1 + ‖x‖) ^ (m * D) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul]
      apply mul_le_mul (hbound s a ha) (norm_monomial_value_le s ?_ x) (abs_nonneg _) (hB s)
      intro i
      exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans (hD a)
    _ ≤ ∑ s ∈ T, B s * (1 + ‖x‖) ^ (m * D) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ =>
        mul_nonneg (hB s) (pow_nonneg (by linarith [norm_nonneg x]) _))
    _ = (∑ s ∈ T, B s) * (1 + ‖x‖) ^ (m * D) := by rw [Finset.sum_mul]
    _ ≤ C * (1 + ‖x‖) ^ (m * D) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith [norm_nonneg x]) _)

theorem exists_uniform_finite_polynomial_growth
    {P J : Type} [TopologicalSpace P] [Fintype J] {m : ℕ}
    (p : J → P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ j a, (p j a).totalDegree ≤ D)
    (heval : ∀ j (x : Fin m → ℝ), Continuous (fun a => eval x (p j a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j a, a ∈ S → ∀ x : Fin m → ℝ,
      |eval x (p j a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  choose C hC hb using (fun j => exists_uniform_polynomial_growth (p j) D (hD j) (heval j) S hS)
  have hC0 : ∀ i, 0 ≤ C i := fun i => (hC i).trans' zero_le_one
  refine ⟨1 + ∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hC0 i)), ?_⟩
  intro j a ha x
  apply (hb j a ha x).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [norm_nonneg x]) _)
  have hj := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ j)
  linarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialDerivativeGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds on growing polynomial input cubes -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set Metric
open scoped BigOperators

theorem continuous_pderiv_evaluation {P : Type} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x, Continuous (fun a => eval x (p a))) (j : Fin m) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (pderiv j (p a))) := by
  apply continuous_polynomial_evaluation_of_coefficients (fun a => pderiv j (p a)) D
    (fun a => (totalDegree_pderiv_le (p a) j).trans ((Nat.sub_le _ _).trans (hD a)))
  intro s
  simp only [coeff_pderiv]
  exact (continuous_polynomial_coefficients p D hD heval _).mul continuous_const

theorem norm_clm_pi_domain_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} (L : (Fin m → ℝ) →L[ℝ] V) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, ‖L (Pi.single j 1)‖ ≤ B) : ‖L‖ ≤ (m : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro x
  have he : L x = ∑ j, x j • L (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ j, x j • L (Pi.single j 1)‖ ≤ ∑ j, ‖x j • L (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖x‖ * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm x j) (hb j) (norm_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * B * ‖x‖ := by simp <;> ring

@[simp] theorem polynomialMapDifferential_basis {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    polynomialMapDifferential p x (Pi.single j 1) i = eval x (pderiv j (p i)) :=
  polynomialDifferential_basis (p i) x j

theorem norm_polynomialMapDifferential_le {m n : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i j, |eval x (pderiv j (p i))| ≤ B) :
    ‖polynomialMapDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [polynomialMapDifferential_basis, Real.norm_eq_abs] using hb i j

theorem norm_polynomialDifferential_le {m : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, |eval x (pderiv j p)| ≤ B) :
    ‖polynomialDifferential p x‖ ≤ (m : ℝ) * B := by
  apply norm_clm_pi_domain_le _ hB
  intro j
  simpa only [polynomialDifferential_basis, Real.norm_eq_abs] using hb j

theorem uniform_polynomial_map_derivative_bounds
    {P : Type} [TopologicalSpace P] {m n : ℕ}
    (p : P → Fin n → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ x, ‖x‖ ≤ R → ‖polynomialMapDifferential (p a) x‖ ≤ C * (1 + R) ^ (m * D)) ∧
      ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖polynomialMapDifferential (p a) x - polynomialMapDifferential (p a) y‖ ≤
          C * (1 + R) ^ (m * D) * dist x y := by
  let p₁ := fun j : Fin n × Fin m => fun a => pderiv j.2 (p a j.1)
  have hD₁ (j : Fin n × Fin m) (a : P) : (p₁ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p a j.1) j.2).trans ((Nat.sub_le _ _).trans (hD a j.1))
  have he₁ (j : Fin n × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₁ j a)) :=
    continuous_pderiv_evaluation (fun a => p a j.1) D (fun a => hD a j.1)
      (heval j.1) j.2 x
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_uniform_finite_polynomial_growth p₁ D hD₁ he₁ S hS
  let p₂ := fun j : (Fin n × Fin m) × Fin m => fun a => pderiv j.2 (p₁ j.1 a)
  have hD₂ (j : (Fin n × Fin m) × Fin m) (a : P) : (p₂ j a).totalDegree ≤ D :=
    (totalDegree_pderiv_le (p₁ j.1 a) j.2).trans ((Nat.sub_le _ _).trans (hD₁ j.1 a))
  have he₂ (j : (Fin n × Fin m) × Fin m) (x : Fin m → ℝ) :
      Continuous (fun a => eval x (p₂ j a)) :=
    continuous_pderiv_evaluation (p₁ j.1) D (hD₁ j.1) (he₁ j.1) j.2 x
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_uniform_finite_polynomial_growth p₂ D hD₂ he₂ S hS
  let C := max 1 (max ((m : ℝ) * C₁) ((m : ℝ) ^ 2 * C₂))
  have hc₁ : (m : ℝ) * C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hc₂ : (m : ℝ) ^ 2 * C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha R hR
  have hpow : 0 ≤ (1 + R) ^ (m * D) := pow_nonneg (by linarith) _
  have hb₁R (i : Fin n) (j : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv j (p a i))| ≤ C₁ * (1 + R) ^ (m * D) :=
    (hb₁ (i, j) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  have hb₂R (i : Fin n) (j k : Fin m) (x : Fin m → ℝ) (hx : ‖x‖ ≤ R) :
      |eval x (pderiv k (pderiv j (p a i)))| ≤ C₂ * (1 + R) ^ (m * D) :=
    (hb₂ ((i, j), k) a ha x).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (by linarith))
  constructor
  · intro x hx
    calc
      _ ≤ (m : ℝ) * (C₁ * (1 + R) ^ (m * D)) :=
        norm_polynomialMapDifferential_le _ _ (mul_nonneg (by linarith) hpow) (fun i j => hb₁R i j x hx)
      _ ≤ C * (1 + R) ^ (m * D) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hc₁ hpow
  · intro x y hx hy
    have hscalar (i : Fin n) (j : Fin m) :
        |eval x (pderiv j (p a i)) - eval y (pderiv j (p a i))| ≤
          (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by
      have h := (convex_closedBall (0 : Fin m → ℝ) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun u _ => (hasFDerivAt_mvPolynomial_eval (pderiv j (p a i)) u).hasFDerivWithinAt)
        (fun u hu => norm_polynomialDifferential_le _ _ (mul_nonneg (by linarith) hpow)
          (fun k => hb₂R i j k u (by simpa only [mem_closedBall, dist_zero_right] using hu)))
        (show y ∈ closedBall 0 R by simpa using hy) (show x ∈ closedBall 0 R by simpa using hx)
      simpa only [Real.norm_eq_abs, dist_eq_norm] using h
    have hB : 0 ≤ (m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y := by positivity
    calc
      _ ≤ (m : ℝ) * ((m : ℝ) * (C₂ * (1 + R) ^ (m * D)) * dist x y) := by
        apply norm_clm_pi_domain_le _ hB
        intro j
        apply (pi_norm_le_iff_of_nonneg hB).mpr
        intro i
        simpa only [sub_apply, Pi.sub_apply,
          polynomialMapDifferential_basis, Real.norm_eq_abs] using hscalar i j
      _ = ((m : ℝ) ^ 2 * C₂) * (1 + R) ^ (m * D) * dist x y := by ring
      _ ≤ C * (1 + R) ^ (m * D) * dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ hpow) dist_nonneg

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialSliceGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growing-cube bounds for the actual derivative minors -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MvPolynomial

theorem norm_finAppend_le {n k : ℕ} {v : Fin n → ℝ} {z : Fin k → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hz : ‖z‖ ≤ R) : ‖Fin.append v z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using (norm_le_pi_norm v j).trans hv
  · intro j
    simpa only [Fin.append_right] using (norm_le_pi_norm z j).trans hz

theorem norm_appendParameterLinear_le (n k : ℕ) : ‖appendParameterLinear n k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, appendParameterLinear_apply]
  exact norm_finAppend_le (norm_nonneg _) le_rfl (by simp)

theorem dist_finAppend_same {n k : ℕ} (v w : Fin n → ℝ) (z : Fin k → ℝ) :
    dist (Fin.append v z) (Fin.append w z) = dist v w := by
  have h := (Fin.appendIsometry (α := ℝ) n k).isometry.dist_eq (v, z) (w, z)
  change dist (Fin.append v z) (Fin.append w z) = dist (v, z) (w, z) at h
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem uniform_polynomial_slice_derivative_bounds
    {P : Type} [TopologicalSpace P] {n k : ℕ}
    (p : P → Fin n → MvPolynomial (Fin (n + k)) ℝ) (D : ℕ)
    (hD : ∀ a i, (p a i).totalDegree ≤ D)
    (heval : ∀ i x, Continuous (fun a => eval x (p a i)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ R : ℝ, 0 ≤ R →
      (∀ v z, ‖v‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z‖ ≤ C * (1 + R) ^ ((n + k) * D)) ∧
      ∀ v w z, ‖v‖ ≤ R → ‖w‖ ≤ R → ‖z‖ ≤ R →
        ‖polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z‖ ≤
          C * (1 + R) ^ ((n + k) * D) * dist v w := by
  obtain ⟨C, hC, hbound⟩ := uniform_polynomial_map_derivative_bounds p D hD heval S hS
  refine ⟨C, hC, ?_⟩
  intro a ha R hR
  obtain ⟨hb, hl⟩ := hbound a ha R hR
  have hnorm (A : (Fin (n + k) → ℝ) →L[ℝ] (Fin n → ℝ)) :
      ‖A.comp (appendParameterLinear n k)‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A‖ * ‖appendParameterLinear n k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (norm_appendParameterLinear_le n k) (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  constructor
  · intro v z hv hz
    exact (hnorm _).trans (hb _ (norm_finAppend_le hR hv hz))
  · intro v w z hv hw hz
    have he : polynomialSliceDifferential (p a) v z - polynomialSliceDifferential (p a) w z =
        (polynomialMapDifferential (p a) (Fin.append v z) -
          polynomialMapDifferential (p a) (Fin.append w z)).comp (appendParameterLinear n k) := by
      ext x i
      rfl
    rw [he]
    exact (hnorm _).trans (by simpa only [dist_finAppend_same] using
      (hl _ _ (norm_finAppend_le hR hv hz) (norm_finAppend_le hR hw hz)))

end PolycyclicRecognition

end

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

theorem sequence_subexponential_lower_const (hs : Tendsto scale atTop atTop)
    {c : ℝ} (hc : 0 < c) : HasSubexponentialLowerBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_lower_const hc).along_sequence hs

theorem HasSubexponentialLowerBoundSeq.min {f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => min (f n) (g n)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with n hn hm
  exact le_min hn hm

theorem HasSubexponentialLowerBoundSeq.inv {f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) :
    HasSubexponentialUpperBoundSeq scale (fun n => (f n)⁻¹) := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  calc
    (f n)⁻¹ ≤ (Real.exp (-ε * scale n))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hn
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_neg]; congr 1; ring

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequencePolynomialValues
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential mass with a subexponential polynomial minor bound -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_large_polynomial_values_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (p : ℕ → MvPolynomial (Fin n) ℝ) (hp : ∀ r, (p r).totalDegree ≤ D)
    (R c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (x₀ : ℕ → Fin n → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin n → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ (η : ℕ → ℝ) (K : ℕ → Set (Fin n → ℝ)),
      (∀ r, 0 < η r) ∧ HasSubexponentialLowerBoundSeq scale η ∧
      (∀ r, K r ⊆ E r) ∧ (∀ r, IsCompact (K r)) ∧
      (∀ r, 0 < (volume (K r)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) ∧
      ∀ r x, x ∈ K r → η r ≤ |MvPolynomial.eval x (p r)| := by
  classical
  obtain ⟨A, hA, hselect⟩ := exists_compact_large_polynomial_values rem n D hn hD
  let m := fun r => (volume (E r)).toReal
  let a := fun r => 2 * A * (1 + R r) ^ n / m r
  let η := fun r => (c r / 2) / a r ^ (n * D)
  have ha (r : ℕ) : 0 < a r := by
    have h := hR r
    have h' := hm r
    dsimp [a, m]
    positivity
  have hη (r : ℕ) : 0 < η r := div_pos (div_pos (hc r) (by norm_num)) (pow_pos (ha r) (n * D))
  have hs (r : ℕ) := hselect (p r) (hp r) (R r) (c r) (hR r) (hc r)
    (x₀ r) (hx₀ r) (hvalue r) (E r) (hE r) (hER r) (hm r)
  choose K hKE hK hmass hgood using hs
  have hR0 : ∀ᶠ r in atTop, 0 ≤ 1 + R r := Eventually.of_forall (fun r => by have := hR r; linarith)
  have haUpper : HasSubexponentialUpperBoundSeq scale a := by
    have hpowers := ((sequence_subexponential_upper_const hscale 1).add hRupper hscale).pow hscale hR0 n
    have hnum := (sequence_subexponential_upper_const hscale (2 * A)).mul hpowers
      (Eventually.of_forall (fun _ => by positivity))
    have hh := hnum.mul hmlower.inv (Eventually.of_forall (fun r => by
      have := hR r
      positivity))
    simpa only [a, m, div_eq_mul_inv] using hh
  have hηlower : HasSubexponentialLowerBoundSeq scale η :=
    (hclower.div (sequence_subexponential_upper_const hscale 2) (Eventually.of_forall (by intro r; norm_num))).div
      (haUpper.pow hscale (Eventually.of_forall (fun r => (ha r).le)) (n * D))
      (Eventually.of_forall (fun r => pow_pos (ha r) (n * D)))
  have hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal) := by
    apply (hmlower.div (sequence_subexponential_upper_const hscale 4) (Eventually.of_forall (by intro r; norm_num))).mono
    exact Eventually.of_forall (fun r => (hmass r).le)
  exact ⟨η, K, hη, hηlower, hKE, hK,
    fun r => (div_pos (hm r) (by norm_num : (0 : ℝ) < 4)).trans (hmass r),
    hKlower, hgood⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential volume of compact noncritical parameter images -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

theorem subexponential_compact_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n : ℕ) (f : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (R L η : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hη : ∀ r, 0 < η r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hηlower : HasSubexponentialLowerBoundSeq scale η)
    (hf : ∀ r z, ‖z‖ ≤ R r + 2 → HasFDerivAt (f r) (df r z) z)
    (hdf : ∀ r z, ‖z‖ ≤ R r + 2 → ‖df r z‖ ≤ L r)
    (hosc : ∀ r z w, ‖z‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r z - df r w‖ ≤ L r * dist z w)
    (K : ℕ → Set (Fin n → ℝ)) (hK : ∀ r, IsCompact (K r))
    (hgood : ∀ r z, z ∈ K r → ‖z‖ ≤ R r ∧ η r ≤ |(df r z).det|)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    (∀ r, IsCompact (f r '' K r)) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' K r)).toReal) := by
  obtain ⟨C, hC, hb⟩ := exists_compact_image_volume_bound n
  let D := fun r => 8 * (C * L r ^ (n - 1)) * L r
  let ρ := fun r => min 1 (η r / D r)
  have hL0 : ∀ᶠ r in atTop, 0 ≤ L r := Eventually.of_forall (fun r => le_trans zero_le_one (hL r))
  have hD : ∀ r, 0 < D r := by
    intro r
    have hLp : 0 < L r := lt_of_lt_of_le zero_lt_one (hL r)
    dsimp [D]
    positivity
  have hDupper : HasSubexponentialUpperBoundSeq scale D := by
    have hp := hLupper.pow hscale hL0 (n - 1)
    have hcp := (sequence_subexponential_upper_const hscale C).mul hp (Eventually.of_forall (fun _ => hC.le))
    have h8 := (sequence_subexponential_upper_const hscale 8).mul hcp (Eventually.of_forall (by intro r; norm_num))
    exact h8.mul hLupper (Eventually.of_forall (by
      intro r
      have hLp : 0 ≤ L r := le_trans zero_le_one (hL r)
      positivity))
  have hρlower : HasSubexponentialLowerBoundSeq scale ρ :=
    (sequence_subexponential_lower_const hscale zero_lt_one).min
      (hηlower.div hDupper (Eventually.of_forall hD))
  have hρpos (r : ℕ) : 0 < ρ r := lt_min zero_lt_one (div_pos (hη r) (hD r))
  let B := fun r => (2 * R r / ρ r + 2) ^ n
  have hBupper : HasSubexponentialUpperBoundSeq scale B := by
    have h2R := (sequence_subexponential_upper_const hscale 2).mul hRupper
      (Eventually.of_forall (by intro r; norm_num))
    have hquot := h2R.mul hρlower.inv (Eventually.of_forall (fun r => mul_nonneg (by norm_num) (hR r)))
    have hsum := hquot.add (sequence_subexponential_upper_const hscale 2) hscale
    simpa only [B, div_eq_mul_inv] using hsum.pow hscale (Eventually.of_forall (by
      intro r
      have h := hR r
      have h' := hρpos r
      positivity)) n
  have hBpos (r : ℕ) : 0 < B r := by
    have h := hR r
    have h' := hρpos r
    dsimp [B]
    positivity
  have hresult (r : ℕ) := hb (f r) (df r) (R r) (L r) (η r)
    (hR r) (hL r) (hη r) (hf r) (hdf r) (hosc r) (K r) (hK r) (hgood r)
  refine ⟨fun r => (hresult r).1, ?_⟩
  apply ((hηlower.mul hKlower).div hBupper (Eventually.of_forall hBpos)).mono
  apply Eventually.of_forall
  intro r
  apply (div_le_iff₀ (hBpos r)).mpr
  simpa only [B, ρ, D, mul_comm] using (hresult r).2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCompactSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact slice retains subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_compact_sections_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (n k : ℕ) (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (K : ℕ → Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hK : ∀ r, IsCompact (K r))
    (hKR : ∀ r p, p ∈ K r → ‖p.2‖ ≤ R r)
    (hKpos : ∀ r, 0 < (volume (K r)).toReal)
    (hKlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (K r)).toReal)) :
    ∃ z : ℕ → Fin k → ℝ,
      (∀ r, ‖z r‖ ≤ R r) ∧
      (∀ r, IsCompact {v | (v, z r) ∈ K r}) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume {v | (v, z r) ∈ K r}).toReal) := by
  classical
  let q := fun r => (2 * R r) ^ k
  let t := fun r => (volume (K r)).toReal / (2 * q r)
  have hqpos (r : ℕ) : 0 < q r := by have := hR r; dsimp [q] <;> positivity
  have htpos (r : ℕ) : 0 < t r := div_pos (hKpos r) (mul_pos (by norm_num) (hqpos r))
  have hs (r : ℕ) : ∃ z ∈ closedBall 0 (R r),
      IsCompact {v | (v, z) ∈ K r} ∧ t r < (volume {v | (v, z) ∈ K r}).toReal := by
    apply exists_compact_section_volume_gt n k (q := q r) (hK r) (isCompact_closedBall _ _)
      (fun p hp => by simpa only [mem_closedBall, dist_zero_right] using hKR r p hp)
      (htpos r).le
    · rw [Real.volume_pi_closedBall _ (by have := hR r; linarith),
        ENNReal.toReal_ofReal (by have := hR r; positivity)]
      simp only [Fintype.card_fin, q, le_refl]
    · have he : t r * q r = (volume (K r)).toReal / 2 := by
        dsimp [t]
        field_simp [ne_of_gt (hqpos r)]
      rw [he]
      linarith [hKpos r]
  choose z hz hzc hmass using hs
  have hqUpper : HasSubexponentialUpperBoundSeq scale q :=
    ((sequence_subexponential_upper_const hscale 2).mul hRupper (Eventually.of_forall (by intro r; norm_num))).pow hscale
      (Eventually.of_forall (fun r => by have := hR r; positivity)) k
  have htLower : HasSubexponentialLowerBoundSeq scale t := hKlower.div
    ((sequence_subexponential_upper_const hscale 2).mul hqUpper (Eventually.of_forall (by intro r; norm_num)))
    (Eventually.of_forall (fun r => mul_pos (by norm_num) (hqpos r)))
  exact ⟨z, fun r => by simpa only [mem_closedBall, dist_zero_right] using hz r,
    hzc, htLower.mono (Eventually.of_forall (fun r => (hmass r).le))⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequencePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact image-volume witnesses for arbitrary measurable parameters

The domain can have more coordinates than the range. The scalar polynomial
is an actual derivative minor. Remez, inner regularity, Fubini, and the
quantitative injective patch estimate provide the compact image witnesses.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_polynomial_image_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (f : ℕ → (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (df : ℕ → (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (p : ℕ → MvPolynomial (Fin (n + k)) ℝ)
    (hp : ∀ r, (p r).totalDegree ≤ D)
    (hminor : ∀ r v z, MvPolynomial.eval (Fin.append v z) (p r) = (df r v z).det)
    (R L c : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hL : ∀ r, 1 ≤ L r)
    (hc : ∀ r, 0 < c r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R) (hLupper : HasSubexponentialUpperBoundSeq scale L)
    (hclower : HasSubexponentialLowerBoundSeq scale c)
    (hf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 →
      HasFDerivAt (fun w => f r (Fin.append w z)) (df r v z) v)
    (hdf : ∀ r z, ‖z‖ ≤ R r → ∀ v, ‖v‖ ≤ R r + 2 → ‖df r v z‖ ≤ L r)
    (hosc : ∀ r z, ‖z‖ ≤ R r → ∀ v w, ‖v‖ ≤ R r + 2 → ‖w‖ ≤ R r + 2 →
      ‖df r v z - df r w z‖ ≤ L r * dist v w)
    (x₀ : ℕ → Fin (n + k) → ℝ) (hx₀ : ∀ r, x₀ r ∈ closedBall 0 (R r))
    (hvalue : ∀ r, c r ≤ |MvPolynomial.eval (x₀ r) (p r)|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ f r '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨η, K, hη, hηlower, hKE, hK, hKpos, hKlower, hgood⟩ :=
    exists_subexponential_large_polynomial_values_sequence scale hscale rem (n + k) D (by omega) hD
      p hp R c hR hc hRupper hclower x₀ hx₀ hvalue E hE hER hm hmlower
  let e := Fin.appendIsometry (α := ℝ) n k
  let K' := fun r => e ⁻¹' K r
  have hK' (r : ℕ) : IsCompact (K' r) := e.toHomeomorph.isCompact_preimage.mpr (hK r)
  have hK'mass (r : ℕ) : volume (K' r) = volume (K r) :=
    (measurePreserving_finAppend n k).measure_preimage (hK r).measurableSet.nullMeasurableSet
  have hbound (r : ℕ) (v : (Fin n → ℝ) × (Fin k → ℝ)) (hv : v ∈ K' r) :
      ‖v‖ ≤ R r := by
    have hb := hER r (hKE r hv)
    have hd := e.dist_eq v 0
    have he0 : e 0 = 0 := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [e]
    rw [he0, dist_zero_right, dist_zero_right] at hd
    simpa only [mem_closedBall, dist_zero_right, hd] using hb
  obtain ⟨z, hz, hs, hsmass⟩ := exists_subexponential_compact_sections_sequence scale hscale n k R hR hRupper
    K' hK' (fun r v hv => (norm_snd_le v).trans (hbound r v hv))
    (fun r => by rw [hK'mass]; exact hKpos r)
    (by simpa only [hK'mass] using hKlower)
  have himage := subexponential_compact_image_sequence scale hscale n
    (fun r v => f r (Fin.append v (z r))) (fun r v => df r v (z r))
    R L η (fun r => (hR r).trans' zero_le_one) hL hη hRupper hLupper hηlower
    (fun r => hf r (z r) (hz r)) (fun r => hdf r (z r) (hz r))
    (fun r => hosc r (z r) (hz r))
    (fun r => {v | (v, z r) ∈ K' r}) hs (fun r v hv => by
      refine ⟨(norm_fst_le (v, z r)).trans (hbound r (v, z r) hv), ?_⟩
      rw [← hminor]
      exact hgood r _ hv) hsmass
  refine ⟨fun r => (fun v => f r (Fin.append v (z r))) '' {v | (v, z r) ∈ K' r},
    himage.1, ?_, himage.2⟩
  intro r y hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨Fin.append v (z r), hKE r hv, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial image volume on subexponentially growing cubes -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem compact_polynomial_family_image_growing_sequence
    {P : Type} [TopologicalSpace P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (c : ℝ) (hc : 0 < c) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : ∀ a ∈ S, c ≤ |(fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀).det|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨D, p, hp, hvalue⟩ := hpoly.exists_uniform_polynomials
  have heval (i : Fin n) (x : Fin (n + k) → ℝ) :
      Continuous (fun a => MvPolynomial.eval x (p a i)) := by
    have harg : Continuous (fun a : P => (a, x)) := continuous_id.prodMk continuous_const
    have h : Continuous (fun a : P => f (a, x) i) := (continuous_apply i).comp (hf.comp harg)
    simpa only [hvalue] using h
  obtain ⟨A, hA, hbounds⟩ := uniform_polynomial_slice_derivative_bounds p D hp heval S hS
  let L := fun r => A * (R r + 3) ^ ((n + k) * D)
  have hL (r : ℕ) : 1 ≤ L r := by
    have hpow : 1 ≤ (R r + 3) ^ ((n + k) * D) := one_le_pow₀ (by linarith [hR r])
    exact one_le_mul_of_one_le_of_one_le hA hpow
  have hRadd : HasSubexponentialUpperBoundSeq scale (fun r => R r + 3) :=
    hRupper.add (sequence_subexponential_upper_const hscale 3) hscale
  have hLupper : HasSubexponentialUpperBoundSeq scale L :=
    (sequence_subexponential_upper_const hscale A).mul
      (hRadd.pow hscale (Eventually.of_forall (fun r => by linarith [hR r])) _)
      (Eventually.of_forall (fun _ => hA.trans' zero_le_one))
  let df := fun r v z => fderiv ℝ (fun w => f (b r, Fin.append w z)) v
  have hdfpoly (a : P) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      fderiv ℝ (fun w => f (a, Fin.append w z)) v = polynomialSliceDifferential (p a) v z := by
    have he : (fun w i => MvPolynomial.eval (Fin.append w z) (p a i)) =
        (fun w => f (a, Fin.append w z)) := by
      funext w i
      exact hvalue a (Fin.append w z) i
    have h := hasFDerivAt_polynomialSlice (p a) v z
    rw [he] at h
    exact h.fderiv
  have hminor (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor (p (b r))) = (df r v z).det := by
    rw [eval_polynomialJacobianMinor, ← hdfpoly]
  have hder (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      HasFDerivAt (fun w => f (b r, Fin.append w z)) (df r v z) v := by
    rw [show df r v z = polynomialSliceDifferential (p (b r)) v z from hdfpoly _ _ _]
    convert hasFDerivAt_polynomialSlice (p (b r)) v z using 1
    all_goals try with_reducible_and_instances rfl
    funext w i
    exact (hvalue (b r) (Fin.append w z) i).symm
  apply exists_subexponential_polynomial_image_sequence scale hscale rem n k (max 1 (n * (D - 1)))
    hn (le_max_left _ _) (fun r x => f (b r, x)) df
    (fun r => polynomialJacobianMinor (p (b r)))
    (fun r => (totalDegree_polynomialJacobianMinor_le _ (hp (b r))).trans (le_max_right _ _))
    hminor R L (fun _ => c) hR hL (fun _ => hc) hRupper hLupper
    (sequence_subexponential_lower_const hscale hc)
    (fun r z _ v _ => hder r v z) (fun r z hz v hv => ?_)
    (fun r z hz v w hv hw => ?_) (fun _ => Fin.append v₀ z₀) hanchor
    (fun r => by rw [hminor]; exact hdet (b r) (hb r)) E hE hER hm hmlower
  · change ‖fderiv ℝ (fun w => f (b r, Fin.append w z)) v‖ ≤ L r
    rw [hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).1 v z hv (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h
  · change ‖fderiv ℝ (fun u => f (b r, Fin.append u z)) v -
      fderiv ℝ (fun u => f (b r, Fin.append u z)) w‖ ≤ L r * dist v w
    rw [hdfpoly, hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).2 v w z hv hw (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingConvergingPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converging polynomial image volume on growing cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_polynomial_family_image_growing_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : (fderiv ℝ (fun v => f (b₀, Fin.append v z₀)) v₀).det ≠ 0)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  let d := fun a => fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀
  have hd : Continuous d := by
    have hg : ContDiff ℝ 2 (fun p : P × (Fin n → ℝ) => f (p.1, Fin.append p.2 z₀)) :=
      hf.comp (contDiff_fst.prodMk
        ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_const)))
    have hh : ContDiff ℝ 1 d := ContDiff.fderiv hg (contDiff_const (c := v₀)) (by norm_num)
    exact hh.continuous
  let D := fun a => |(d a).det|
  have hD : Continuous D := (continuous_det_clm hd).abs
  have hDpos : 0 < D b₀ := abs_pos.mpr hdet
  let c := D b₀ / 2
  have hc : 0 < c := half_pos hDpos
  let T := S ∩ {a | c ≤ D a}
  have hT : IsCompact T := hS.inter_right (isClosed_le continuous_const hD)
  have hb₀T : b₀ ∈ T := ⟨hb₀, (half_le_self hDpos.le)⟩
  have hlate : ∀ᶠ r in atTop, b r ∈ T := by
    have hh := (hD.continuousAt.tendsto.comp hlim).eventually
      (Ioi_mem_nhds (show c < D b₀ from half_lt_self hDpos))
    filter_upwards [hh] with r hr
    exact ⟨hb r, hr.le⟩
  let b' := fun r => if b r ∈ T then b r else b₀
  have hb' : ∀ r, b' r ∈ T := by
    intro r
    dsimp [b']
    split_ifs with h
    · exact h
    · exact hb₀T
  obtain ⟨C, hC, hCE, hClower⟩ := compact_polynomial_family_image_growing_sequence
    scale hscale rem n k hn f hf.continuous hpoly T hT b' hb' R hR hRupper c hc v₀ z₀ hanchor
    (fun a ha => ha.2) E hE hER hm hmlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hlate] with r hr
  simpa only [b', ite_eq_left hr] using hCE r

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingSubmersivePolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Submersive polynomial images on growing input cubes -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem converging_submersive_polynomial_image_growing_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (t₀ : Fin m → ℝ) (ht₀ : ∀ r, ‖t₀‖ ≤ R r)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  classical
  obtain ⟨j, hj, hminor⟩ := exists_nonsingular_column_minor
    (fderiv ℝ (fun x => f (b₀, x)) t₀).toLinearMap hs
  obtain ⟨k, e, he⟩ := exists_fin_equiv_extending_injection j hj
  let u₀ := reindexParameters e.symm t₀
  let v₀ := fun i : Fin n => u₀ (Fin.castAdd k i)
  let z₀ := fun i : Fin k => u₀ (Fin.natAdd n i)
  have hu : Fin.append v₀ z₀ = u₀ := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [v₀, z₀]
  have hback : reindexParameters e (Fin.append v₀ z₀) = t₀ := by
    rw [hu]
    ext i
    simp [u₀]
  let g := fun p : P × (Fin (n + k) → ℝ) => f (p.1, reindexParameters e p.2)
  have hg : ContDiff ℝ 2 g :=
    hf.comp (contDiff_fst.prodMk ((reindexParameters e).contDiff.comp contDiff_snd))
  have hgpoly : HasPolynomialCoordinates (fun a x => g (a, x)) :=
    fun i => (hpoly i).reindex e
  have hd : (fderiv ℝ (fun v => g (b₀, Fin.append v z₀)) v₀).det ≠ 0 := by
    have hfd : DifferentiableAt ℝ (fun x => f (b₀, x))
        (reindexParameters e (Fin.append v₀ z₀)) := by
      rw [hback]
      exact ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)).differentiableAt
    rw [show (fun v => g (b₀, Fin.append v z₀)) =
      (fun v => f (b₀, reindexParameters e (Fin.append v z₀))) from rfl,
      det_reindexed_slice e (fun x => f (b₀, x)) v₀ z₀ hfd, hback]
    simpa only [he, ContinuousLinearMap.coe_coe] using hminor
  let E' := fun r => reindexParameters e ⁻¹' E r
  have hE' : ∀ r, MeasurableSet (E' r) :=
    fun r => (hE r).preimage (reindexParameters e).continuous.measurable
  have hvol (r : ℕ) : volume (E' r) = volume (E r) :=
    (measurePreserving_reindexParameters e).measure_preimage (hE r).nullMeasurableSet
  have hER' (r : ℕ) : E' r ⊆ closedBall 0 (R r) := by
    intro x hx
    have hh := hER r hx
    simpa only [mem_closedBall, dist_zero_right, reindexParameters_norm] using hh
  have hanchor (r : ℕ) : Fin.append v₀ z₀ ∈ closedBall 0 (R r) := by
    rw [hu, mem_closedBall, dist_zero_right, reindexParameters_norm]
    exact ht₀ r
  obtain ⟨C, hC, hCE, hClower⟩ := converging_polynomial_family_image_growing_sequence
    scale hscale rem n k hn g hg hgpoly S hS b hb b₀ hb₀ hlim R hR hRupper v₀ z₀ hanchor hd
    E' hE' hER' (fun r => by rw [hvol]; exact hm r) (by simpa only [hvol] using hmlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCE] with r hr
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := hr hy
  exact ⟨reindexParameters e x, hx, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_GrowingEventualPolynomialImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growing-cube image volume for successful measurable parameters -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem converging_submersive_polynomial_image_growing_eventual_sequence
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m n : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (f : P × (Fin m → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (b₀ : P) (hb₀ : b₀ ∈ S) (hlim : Tendsto b atTop (𝓝 b₀))
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (t₀ : Fin m → ℝ) (ht₀ : ∀ r, ‖t₀‖ ≤ R r)
    (hs : Function.Surjective (fderiv ℝ (fun x => f (b₀, x)) t₀))
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨E', hE', hER', hm', hlower', heq⟩ :=
    exists_positive_parameter_sets_growing_sequence R scale
      (fun r => lt_of_lt_of_le zero_lt_one (hR r)) E hE hER hmlower
  obtain ⟨C, hC, hCE, hlower⟩ := converging_submersive_polynomial_image_growing_sequence
    scale hscale rem hn f hf hpoly S hS b hb b₀ hb₀ hlim R hR hRupper t₀ ht₀ hs E' hE' hER' hm' hlower'
  refine ⟨C, hC, ?_, hlower⟩
  filter_upwards [hCE, heq] with r hr he
  simpa only [he] using hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingProductImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image volume for the limiting alternating product -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem alternating_product_image_growing_sequence
    {m n h c : ℕ} (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ n)
    (p : ℕ → AlternatingLawData n) (p₀ : AlternatingLawData n)
    (hlim : Tendsto p atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin n → ℝ) × (Fin n → ℝ))
    (hs : Function.Surjective (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (E : ℕ → Set (Fin m → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ flatAlternatingProduct a e (p r) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  let R' := fun r => R r + (1 + ‖e.symm z₀‖)
  have hR' (r : ℕ) : 1 ≤ R' r := by dsimp [R'] <;> linarith [hR r, norm_nonneg (e.symm z₀)]
  have hRupper' : HasSubexponentialUpperBoundSeq scale R' :=
    hRupper.add (sequence_subexponential_upper_const hscale (1 + ‖e.symm z₀‖)) hscale
  apply converging_submersive_polynomial_image_growing_eventual_sequence scale hscale rem hn
    (fun z => flatAlternatingProduct a e z.1 z.2)
    (contDiff_flatAlternatingProduct a e) (hasPolynomialCoordinates_flatAlternatingProduct a e)
    (insert p₀ (range p)) hlim.isCompact_insert_range p
    (fun r => mem_insert_of_mem _ (mem_range_self r)) p₀ (mem_insert _ _) hlim
    R' hR' hRupper' (e.symm z₀) (fun r => by dsimp [R'] <;> linarith [hR r])
    (flatAlternatingProduct_submersive a e p₀ z₀ hs) E hE _ hmlower
  intro r x hx
  apply mem_closedBall_zero_iff.mpr
  exact (mem_closedBall_zero_iff.mp (hER r hx)).trans
    (by dsimp [R'] <;> linarith [norm_nonneg (e.symm z₀)])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BundleParameterCharts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual global interval coordinates, grouped into source bundles -/

noncomputable section
namespace PolycyclicRecognition

theorem bundleParameterIndex_left (h m : ℕ) (i : Fin h) (j : Fin m) :
    bundleParameterIndex h m (i, Fin.castAdd m j) =
      Fin.castAdd (h * m) (finProdFinEquiv (i, j)) := by
  simp only [bundleParameterIndex, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.prodSumDistrib_apply_left, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

theorem bundleParameterIndex_right (h m : ℕ) (i : Fin h) (j : Fin m) :
    bundleParameterIndex h m (i, Fin.natAdd m j) =
      Fin.natAdd (h * m) (finProdFinEquiv (i, j)) := by
  simp only [bundleParameterIndex, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.prodSumDistrib_apply_right, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupedGoodWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successful switch words remain good at every bundle boundary -/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

omit [Group G] in
theorem ofFn_eq_flatten_bundles {h m : ℕ} (u : Fin (h * m) → G) :
    List.ofFn u = (List.ofFn (fun i : Fin h =>
      List.ofFn (fun j : Fin m => u (finProdFinEquiv (i, j))))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingWordOrder
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chronological alternating words and the two polynomial input blocks -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

theorem alternatingWordIndex_left (h : ℕ) (i : Fin h) :
    alternatingWordIndex h (finProdFinEquiv (i, (0 : Fin 2))) = Fin.castAdd h i := by
  simp only [alternatingWordIndex, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  rw [bundleParameterIndex_left]
  apply Fin.ext
  simp [finProdFinEquiv]

theorem alternatingWordIndex_right (h : ℕ) (i : Fin h) :
    alternatingWordIndex h (finProdFinEquiv (i, (1 : Fin 2))) = Fin.natAdd h i := by
  simp only [alternatingWordIndex, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  rw [bundleParameterIndex_right]
  apply Fin.ext
  simp [finProdFinEquiv]

variable {G : Type} [MeasurableSpace G]

theorem alternatingWordBlockEquiv_left (h : ℕ) (u : Fin (h * 2) → G) (i : Fin h) :
    alternatingWordBlockEquiv h u (Fin.castAdd h i) = u (finProdFinEquiv (i, (0 : Fin 2))) := by
  rw [← alternatingWordIndex_left h i]
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

theorem alternatingWordBlockEquiv_right (h : ℕ) (u : Fin (h * 2) → G) (i : Fin h) :
    alternatingWordBlockEquiv h u (Fin.natAdd h i) = u (finProdFinEquiv (i, (1 : Fin 2))) := by
  rw [← alternatingWordIndex_right h i]
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

theorem alternatingWordBlockEquiv_apply (h : ℕ) (u : Fin (h * 2) → G) (i : Fin (h + h)) :
    alternatingWordBlockEquiv h u i = u ((alternatingWordIndex h).symm i) := by
  simp [alternatingWordBlockEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem measurePreserving_alternatingWordBlockEquiv (h : ℕ)
    (μ : Measure G) [SigmaFinite μ] :
    MeasurePreserving (alternatingWordBlockEquiv (G := G) h)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
  measurePreserving_piCongrLeft (fun _ => μ) (alternatingWordIndex h)

theorem alternatingWordBlockEquiv_image_measure (h : ℕ)
    (μ : Measure G) [SigmaFinite μ] (S : Set (Fin (h * 2) → G)) :
    (Measure.pi fun _ : Fin (h + h) => μ) (alternatingWordBlockEquiv h '' S) =
      (Measure.pi fun _ : Fin (h * 2) => μ) S := by
  let e := alternatingWordBlockEquiv (G := G) h
  have hm := (measurePreserving_alternatingWordBlockEquiv h μ).map_eq
  have he := congrArg (fun ν : Measure (Fin (h + h) → G) => ν (e '' S)) hm
  rw [e.measurableEmbedding.map_apply, Set.preimage_image_eq _ e.injective] at he
  exact he.symm

theorem continuous_alternatingWordBlockEquiv [TopologicalSpace G] (h : ℕ) :
    Continuous (alternatingWordBlockEquiv (G := G) h) := by
  have he : (alternatingWordBlockEquiv (G := G) h : _ → _) =
      fun u i => u ((alternatingWordIndex h).symm i) :=
    funext (fun u => funext (alternatingWordBlockEquiv_apply h u))
  rw [he]
  exact continuous_pi (fun i => continuous_apply ((alternatingWordIndex h).symm i))

theorem alternatingWordBlockEquiv_prod [Group G] (h : ℕ) (u : Fin (h * 2) → G) :
    (List.ofFn (fun i : Fin h =>
      alternatingWordBlockEquiv h u (Fin.castAdd h i) *
        alternatingWordBlockEquiv h u (Fin.natAdd h i))).prod = (List.ofFn u).prod := by
  simp only [alternatingWordBlockEquiv_left, alternatingWordBlockEquiv_right]
  rw [ofFn_eq_flatten_bundles, List.prod_flatten, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TupleMeasureScaling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent coordinate changes and their product-volume multiplier -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem measure_pi_smul {I : Type} [Fintype I]
    {X : I → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : I → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    Finset.prod_mul_distrib]

theorem map_pi_of_coordinate_scaling {I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i))
    (c : I → ℝ≥0) (hmap : ∀ i, Measure.map (f i) (μ i) = c i • ν i) :
    Measure.map (fun x i => f i (x i)) (Measure.pi μ) = (∏ i, c i) • Measure.pi ν := by
  let : ∀ i, SigmaFinite (Measure.map (f i) (μ i)) := fun i => by
    rw [hmap i]
    first | exact Measure.isProbabilityMeasure_map (by first | exact (hf i).aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  simp_rw [hmap]
  exact measure_pi_smul ν c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialTupleCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product volume under independent exponential coordinate charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal NNReal BigOperators

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialBasisHomeomorph_apply {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) (x : Fin n → ℝ) :
    exponentialBasisHomeomorph e chart b x = Exp (e (b.equivFun.symm x)) := hchart _

theorem map_exponentialBasisHomeomorph_inverse {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ b : Basis (Fin n) ℝ L) :
    Measure.map (exponentialBasisHomeomorph e chart b).symm
      (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume) =
        basisVolumeMultiplier b₀ b • (volume : Measure (Fin n → ℝ)) := by
  ext S hS
  rw [Measure.map_apply (exponentialBasisHomeomorph e chart b).symm.measurable hS,
    Measure.smul_apply]
  have hpre : (exponentialBasisHomeomorph e chart b).symm ⁻¹' S =
      ((Exp ∘ e) ∘ b.equivFun.symm) '' S := by
    rw [(exponentialBasisHomeomorph e chart b).preimage_symm]
    congr 1
    funext x
    exact exponentialBasisHomeomorph_apply e Exp chart hchart b x
  rw [hpre, exponential_basis_subset_measure e Exp chart hchart]
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
  rfl

theorem map_exponential_tuple_coordinates {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) :
    Measure.map (fun u i => (exponentialBasisHomeomorph e chart (b i)).symm (u i))
      (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) =
        (∏ i, basisVolumeMultiplier b₀ (b i)) •
          (volume : Measure (Fin h → Fin n → ℝ)) := by
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  have he : ((Exp ∘ e) ∘ b₀.equivFun.symm) = exponentialBasisHomeomorph e chart b₀ := by
    funext x
    exact (exponentialBasisHomeomorph_apply e Exp chart hchart b₀ x).symm
  let : SigmaFinite μ := by
    dsimp only [μ]
    rw [he]
    exact (exponentialBasisHomeomorph e chart b₀).measurableEmbedding.sigmaFinite_map
  exact map_pi_of_coordinate_scaling (fun _ : Fin h => μ) (fun _ : Fin h => volume)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm.measurable)
    (fun i => basisVolumeMultiplier b₀ (b i))
    (fun i => map_exponentialBasisHomeomorph_inverse e Exp chart hchart b₀ (b i))

theorem exponential_tuple_subset_measure {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(b₀.toMatrix (b i)).det|) *
        volume (exponentialTupleCoordinates e chart b '' S) := by
  let : SecondCountableTopology G := (exponentialBasisHomeomorph e chart b₀).symm.secondCountableTopology
  let f := exponentialTupleCoordinates e chart b
  have hm := map_exponential_tuple_coordinates e Exp chart hchart b₀ b
  change Measure.map f _ = _ at hm
  have hv := congrArg (fun μ : Measure (Fin h → Fin n → ℝ) => μ (f '' S)) hm
  rw [f.measurableEmbedding.map_apply, Set.preimage_image_eq _ f.injective,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hv
  rw [hv]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  exact map_prod NNReal.toRealHom (fun i => basisVolumeMultiplier b₀ (b i)) Finset.univ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TupleCoordinateBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds in the actual inverse exponential charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Metric
open scoped Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialBasisHomeomorph_symm_exp {n : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) (v : L) :
    (exponentialBasisHomeomorph lie chart b).symm (Exp (lie v)) = b.equivFun v := by
  apply (exponentialBasisHomeomorph lie chart b).injective
  rw [Homeomorph.apply_symm_apply, exponentialBasisHomeomorph_apply lie Exp chart hchart,
    LinearEquiv.symm_apply_apply]

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialTupleCoordinates_image_subset_ball {n h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Fin h → Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R)
    (S : Set (Fin h → G))
    (hS : ∀ u ∈ S, ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie) (b i) R) :
    exponentialTupleCoordinates lie chart b '' S ⊆ closedBall 0 R := by
  rintro z ⟨u, hu, rfl⟩
  apply mem_closedBall_zero_iff.mpr
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  obtain ⟨v, hv, hb⟩ := hS u hu i
  change ‖(exponentialBasisHomeomorph lie chart (b i)).symm (u i)‖ ≤ R
  rw [← hv]
  simpa only [Function.comp_apply, exponentialBasisHomeomorph_symm_exp lie Exp chart hchart] using hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearHaarCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed linear coordinates preserve subexponential volume rates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V] [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [Measure.IsAddHaarMeasure (volume : Measure W)]

omit [FiniteDimensional ℝ W] in
theorem linear_equiv_volume_image_factor (e : V ≃L[ℝ] W) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : Set V,
      volume (e '' S) = ENNReal.ofReal c * volume S := by
  let c := Measure.addHaarScalarFactor (Measure.map e.symm volume) (volume : Measure V)
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c, hc, ?_⟩
  intro S
  have hm := Measure.isAddLeftInvariant_eq_smul_of_regular
    (Measure.map e.symm volume) (volume : Measure V)
  have he := congrArg (fun μ : Measure V => μ S) hm
  change (Measure.map e.toHomeomorph.symm volume) S = _ at he
  rw [e.toHomeomorph.symm.measurableEmbedding.map_apply,
    e.toHomeomorph.preimage_symm, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at he
  simpa only [c, ENNReal.ofReal_coe_nnreal, ContinuousLinearEquiv.coe_toHomeomorph] using he

omit [FiniteDimensional ℝ W] in
theorem HasSubexponentialLowerBoundSeq.linear_image {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (e : V ≃L[ℝ] W)
    {A : ℕ → Set V}
    (hA : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (e '' A r)).toReal) := by
  obtain ⟨c, hc, hm⟩ := linear_equiv_volume_image_factor e
  have he (r : ℕ) : (volume (e '' A r)).toReal = c * (volume (A r)).toReal := by
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  simpa only [he] using (sequence_subexponential_lower_const hscale hc).mul hA

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledTupleVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of correlated tuple volume

The domain is an arbitrary tuple set. Its coordinates need not be
independent after the successful parameters have been retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold ENNReal Topology BigOperators

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem exponential_rescaled_tuple_subset_measure {h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (r : ℝ) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|) *
        ENNReal.ofReal (Real.exp (r * ∑ i, columnBasisWeight (cost i) (β i).val)) *
        volume (exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost r) '' S) := by
  rw [exponential_tuple_subset_measure e Exp chart hchart b₀
    (rescaledTupleBases X words β cost r) S]
  have hd (i : Fin h) : |(b₀.toMatrix (rescaledTupleBases X words β cost r i)).det| =
      |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det| *
        Real.exp (r * columnBasisWeight (cost i) (β i).val) := by
    change |(b₀.toMatrix (exponentialRescaleBasis
      (WordBasisSelections.basis X words (β i))
      (fun j => cost i ((β i).val j)) r)).det| = _
    rw [← scaledColumnMatrix_eq_basis_toMatrix, det_scaledColumnMatrix,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_comm _ _
  rw [Finset.prod_congr rfl (fun i _ => hd i)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
    ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => abs_nonneg _)), mul_assoc]

theorem rescaled_tuple_volume_lower_sequence {h : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (S : ℕ → Set (Fin h → G))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) (S n)).toReal /
        Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val))) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      (volume (exponentialTupleCoordinates e chart
        (rescaledTupleBases X words β cost (scale n)) '' S n)).toReal) := by
  let d := ∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|
  have hd : 0 < d := Finset.prod_pos (fun i _ => abs_pos.mpr (wordBasis_det_ne_zero X words b₀ (β i)))
  have he (n : ℕ) :
      (((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        (S n)).toReal / Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val)) / d =
      (volume (exponentialTupleCoordinates e chart
        (rescaledTupleBases X words β cost (scale n)) '' S n)).toReal := by
    rw [exponential_rescaled_tuple_subset_measure e Exp chart hchart X words b₀ β cost (scale n) (S n)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  have h := hlower.div (sequence_subexponential_upper_const hscale d)
    (Eventually.of_forall (fun _ => hd))
  simpa only [he] using h


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedTupleDomain
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A correlated tuple set in a growing flat coordinate cube -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter Metric
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem normalized_tuple_domain {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin h → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (S : ℕ → Set (Fin h → G)) (hS : ∀ r, IsCompact (S r))
    (hbox : ∀ r u, u ∈ S r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words β cost (scale r) i) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume))
        (S r)).toReal / Real.exp (scale r * ∑ i, columnBasisWeight (cost i) (β i).val))) :
    let f := fun r => flatExponentialTupleCoordinates lie chart
      (rescaledTupleBases X words β cost (scale r)) flat
    (∀ r, IsCompact (f r '' S r)) ∧
    (∀ r, f r '' S r ⊆ closedBall 0 (‖flat.symm.toContinuousLinearMap‖ * R r)) ∧
    HasSubexponentialUpperBoundSeq scale (fun r => ‖flat.symm.toContinuousLinearMap‖ * R r) ∧
    HasSubexponentialLowerBoundSeq scale (fun r => (volume (f r '' S r)).toReal) := by
  dsimp only
  refine ⟨fun r => (hS r).image (Homeomorph.continuous _), ?_, ?_, ?_⟩
  · intro r z hz
    obtain ⟨u, hu, rfl⟩ := hz
    apply mem_closedBall_zero_iff.mpr
    have hb := exponentialTupleCoordinates_image_subset_ball lie Exp chart hchart
      (rescaledTupleBases X words β cost (scale r)) (hR r) (S r) (hbox r)
    exact (flat.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (hb ⟨u, hu, rfl⟩)) (norm_nonneg _))
  · exact (sequence_subexponential_upper_const hscale ‖flat.symm.toContinuousLinearMap‖).mul hRupper
      (Eventually.of_forall (fun _ => norm_nonneg _))
  · have h := (rescaled_tuple_volume_lower_sequence scale hscale lie Exp chart hchart
      X words b₀ β cost S hlower).linear_image hscale flat.symm
    have he (r : ℕ) :
        flatExponentialTupleCoordinates lie chart (rescaledTupleBases X words β cost (scale r)) flat '' S r =
        flat.symm '' (exponentialTupleCoordinates lie chart
          (rescaledTupleBases X words β cost (scale r)) '' S r) := by
      rw [← Set.image_comp]
      rfl
    simpa only [he] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceFiniteSubexponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One subexponential radius for a fixed finite family of boxes -/

namespace PolycyclicRecognition

open Filter
open scoped Topology BigOperators

theorem HasSubexponentialUpperBoundSeq.finset_sum {I : Type}
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop) (s : Finset I)
    (f : I → ℕ → ℝ) (hf : ∀ i ∈ s, HasSubexponentialUpperBoundSeq scale (f i)) :
    HasSubexponentialUpperBoundSeq scale (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sequence_subexponential_upper_const hs 0
  | @insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h₁.add h₂ hs

theorem finite_subexponential_envelope {I : Type} [Fintype I]
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (f : I → ℕ → ℝ) (hf0 : ∀ i n, 0 ≤ f i n)
    (hf : ∀ i, HasSubexponentialUpperBoundSeq scale (f i)) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ i n, f i n ≤ R n := by
  classical
  refine ⟨fun n => ∑ i, f i n, fun n => Finset.sum_nonneg (fun i _ => hf0 i n),
    HasSubexponentialUpperBoundSeq.finset_sum hs Finset.univ f (fun i _ => hf i), ?_⟩
  intro i n
  exact Finset.single_le_sum (fun j _ => hf0 j n) (Finset.mem_univ i)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ShortSheetBridges
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short bridges between the two sheets at a common pivot -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_short_path_of_minimizing_paths
    {G : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (a b : G) :
    ∃ γ : Path a b, PathMetricBound γ (dist a b) 0 := by
  obtain ⟨f, hf0, hf1, hf⟩ := hpath (a⁻¹ * b)
  have hd : dist (1 : G) (a⁻¹ * b) = dist a b := by
    simpa only [mul_one, mul_inv_cancel_left] using
      (dist_mul_left a (1 : G) (a⁻¹ * b)).symm
  have hlip : LipschitzWith ⟨dist a b, dist_nonneg⟩ (fun t : unitInterval => f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change dist (f s) (f t) ≤ dist a b * dist s t
    rw [Subtype.dist_eq, Real.dist_eq, ← hd]
    exact hf s s.property t t.property
  let γ : Path a b := {
    toFun := fun t => a * f t
    continuous_toFun := continuous_const.mul hlip.continuous
    source' := by simp only [Icc.coe_zero, hf0, mul_one]
    target' := by simp only [Icc.coe_one, hf1, mul_inv_cancel_left] }
  refine ⟨γ, ?_⟩
  intro s t
  change dist (a * f s) (a * f t) ≤ _
  rw [dist_mul_left, add_zero]
  simpa only [hd] using hf s s.property t t.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TemplateThickeningLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.SupportDatum.transport_weight_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the final height-template enlargement -/

namespace PolycyclicRecognition.SupportDatum

open Set Metric
open scoped Pointwise

variable {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : SupportDatum W I B)

/-- An exponent bounded by every positive thickening is bounded by the
original compact template. -/
theorem le_templateSupport_of_thickenings {E : Set W} (hE : IsCompact E)
    (hne : E.Nonempty) {p : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → p ≤ D.templateSupport (E + closedBall 0 ε)) :
    p ≤ D.templateSupport E := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (D.templateSupportConstant + 1)
  have hε : 0 < ε := div_pos hη (by linarith [D.templateSupportConstant_nonneg])
  have hn : (E + closedBall (0 : W) ε).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z + 0, add_mem_add hz (by simpa using hε.le)⟩
  have hu := D.templateSupport_le_of_nearby (hE.add (isCompact_closedBall 0 ε)) hn
    hE hε.le (show ∀ x ∈ E + closedBall 0 ε, ∃ y ∈ E, ‖x - y‖ ≤ ε by
      rintro x ⟨y, hy, u, hu, rfl⟩
      refine ⟨y, hy, ?_⟩
      simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hu)
  have hsmall : D.templateSupportConstant * ε ≤ η := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [D.templateSupportConstant_nonneg])).mpr
    nlinarith
  exact (h ε hε).trans (hu.trans (add_le_add le_rfl hsmall))

end PolycyclicRecognition.SupportDatum

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateChartSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinate maps of the actual two-factor chart samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

/-- A Lie-algebra identification transports the same binary Dynkin formula. -/
theorem model_binary_dynkin
    {L L' N : Type} [LieRing L] [LieAlgebra ℝ L]
    [LieRing L'] [LieAlgebra ℝ L'] [Group N]
    (e : L ≃ₗ⁅ℝ⁆ L') (Exp : L' → N) {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : L) :
    Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y) := by
  have he := congrArg Exp (finiteDynkinPolynomial_map e.toLieHom a ![x, y])
  have hv : (fun i => e.toLieHom (![x, y] i)) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact he.trans (hm (e x) (e y))

/-- The coordinate Dynkin product maps to the actual group product. -/
theorem exp_basis_dynkinProduct
    {L N : Type} [LieRing L] [LieAlgebra ℝ L] [Group N]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (Exp : L → N)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
      Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
  have h := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply, hm]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledWordEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group endpoints in rescaled logarithmic coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G I : Type} [LieRing L] [LieAlgebra ℝ L] [Group G] {n c m : ℕ}

theorem exp_basis_listProduct (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (xs : List (Fin n → ℝ)) :
    Exp (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs)) =
      (xs.map (fun x => Exp (b.equivFun.symm x))).prod := by
  induction xs with
  | nil => simpa [polynomialListProduct] using hzero
  | cons x xs ih =>
    simp only [polynomialListProduct, List.map_cons, List.prod_cons]
    have he := basis_dynkinProduct b a (b.equivFun.symm x)
      (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs))
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm, ih]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledAlternatingEndpoints
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The alternating coordinate map is the actual nilpotent product -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L G : Type} [LieRing L] [LieAlgebra ℝ L] [Group G]

theorem exp_basis_alternatingProduct {n h c : ℕ}
    (b b₁ b₂ : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (z : Fin h → (Fin n → ℝ) × (Fin n → ℝ)) :
    Exp (b.equivFun.symm (alternatingCoordinateProduct a (basisBracket b)
      (boxCoordinateChange b b₁) (boxCoordinateChange b b₂) z)) =
      (List.ofFn (fun j => Exp (b₁.equivFun.symm (z j).1) *
        Exp (b₂.equivFun.symm (z j).2))).prod := by
  unfold alternatingCoordinateProduct
  rw [exp_basis_listProduct b Exp hzero a hm, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  rw [exp_basis_dynkinProduct b Exp a hm]
  simp only [boxCoordinateChange_apply, LinearEquiv.symm_apply_apply]

theorem exp_flatAlternatingProduct {m n h c : ℕ}
    (b b₁ b₂ : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (x : Fin m → ℝ) :
    Exp (b.equivFun.symm (flatAlternatingProduct a e
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂) x)) =
      (List.ofFn (fun j => Exp (b₁.equivFun.symm (e x j).1) *
        Exp (b₂.equivFun.symm (e x j).2))).prod :=
  exp_basis_alternatingProduct b b₁ b₂ Exp hzero a hm (e x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AlternatingHaarImage
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar-volume rate of the actual alternating product

The compact coordinate image furnished by scalar Remez is transported
through the actual exponential chart. The output determinant is the
weight of the union template, not the sum of the input weights.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem alternating_haar_image_growing_sequence {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ)
    (b₁ b₂ : ℕ → Basis (Fin (finrank ℝ L)) ℝ L)
    (e : (Fin m → ℝ) ≃L[ℝ]
      (Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ)))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ finrank ℝ L)
    (p₀ : AlternatingLawData (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      (basisBracket b, boxCoordinateChange b (b₁ r), boxCoordinateChange b (b₂ r)))
      atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r)
    (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (A : ℕ → Set (Fin m → ℝ)) (hA : ∀ r, MeasurableSet (A r))
    (hAR : ∀ r, A r ⊆ Metric.closedBall 0 (R r))
    (hAlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (A r)).toReal)) :
    ∃ C : ℕ → Set G,
      (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun x => (List.ofFn (fun j =>
        Exp (lie ((b₁ r).equivFun.symm (e x j).1)) *
        Exp (lie ((b₂ r).equivFun.symm (e x j).2)))).prod) '' A r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β)
    (fun j => cost (β.val j)) (scale r)
  let p : ℕ → AlternatingLawData (finrank ℝ L) := fun r =>
    (basisBracket (b r), boxCoordinateChange (b r) (b₁ r), boxCoordinateChange (b r) (b₂ r))
  obtain ⟨K, hK, hKA, hKlower⟩ := alternating_product_image_growing_sequence a e
    scale hscale rem hn p p₀ hlim z₀ hs R hR hRupper A hA hAR hAlower
  let f := fun r => (Exp ∘ lie) ∘ (b r).equivFun.symm
  have hf (r : ℕ) : f r = exponentialBasisHomeomorph lie chart (b r) := by
    funext x
    exact (exponentialBasisHomeomorph_apply lie Exp chart hchart (b r) x).symm
  refine ⟨fun r => f r '' K r, fun r => (hK r).image (by rw [hf]; fun_prop), ?_, ?_⟩
  · filter_upwards [hKA] with r hr
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hr hz
    refine ⟨x, hx, ?_⟩
    rw [← hxy]
    exact (exp_flatAlternatingProduct (b r) (b₁ r) (b₂ r) (Exp ∘ lie)
      (by simpa using hzero) a (model_binary_dynkin lie Exp a hm) e x).symm
  · let d := |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det|
    have hd : 0 < d := abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β)
    have he (r : ℕ) :
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (f r '' K r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val) = d * (volume (K r)).toReal := by
      rw [exponential_rescaled_subset_measure lie Exp chart hchart X words b₀ β cost
        (scale r) (K r)]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
      field_simp
    simpa only [he] using (sequence_subexponential_lower_const hscale hd).mul hKlower

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CorrelatedAlternatingHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Alternating products of correlated lifted tuples

No independence is required of the retained tuple set. The product rank
is a property of the full limiting multiplication map.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem correlated_alternating_haar_image {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β β₁ β₂ : WordBasisSelections X words) (cost cost₁ cost₂ : words → ℝ)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin (h + h) → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ finrank ℝ L)
    (p₀ : AlternatingLawData (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      let b₁ := exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
        (fun j => cost₁ (β₁.val j)) (scale r)
      let b₂ := exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
        (fun j => cost₂ (β₂.val j)) (scale r)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (S : ℕ → Set (Fin (h + h) → G)) (hS : ∀ r, IsCompact (S r))
    (hbox : ∀ r u, u ∈ S r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words (Fin.addCases (fun _ => β₁) (fun _ => β₂))
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂)) (scale r) i) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin (h + h) =>
        Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (S r)).toReal /
      Real.exp (scale r * ∑ i : Fin (h + h), columnBasisWeight
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂) i)
        ((Fin.addCases (motive := fun _ : Fin (h + h) => WordBasisSelections X words)
          (fun _ => β₁) (fun _ => β₂) i).val)))) :
    ∃ C : ℕ → Set G, (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun u : Fin (h + h) → G =>
        (List.ofFn (fun j : Fin h => u (Fin.castAdd h j) * u (Fin.natAdd h j))).prod) '' S r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let pairβ : Fin (h + h) → WordBasisSelections X words :=
    Fin.addCases (fun _ => β₁) (fun _ => β₂)
  let pairCost : Fin (h + h) → words → ℝ :=
    Fin.addCases (fun _ => cost₁) (fun _ => cost₂)
  let bs := fun r => rescaledTupleBases X words pairβ pairCost (scale r)
  let f := fun r => flatExponentialTupleCoordinates lie chart (bs r) flat
  let A := fun r => f r '' S r
  obtain ⟨hAc, hAR, hRflat, hAlower⟩ := normalized_tuple_domain lie Exp chart hchart X words b₀
    pairβ pairCost
    flat scale hscale R hR hRupper S hS hbox hlower
  let b₁ := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
    (fun j => cost₁ (β₁.val j)) (scale r)
  let b₂ := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
    (fun j => cost₂ (β₂.val j)) (scale r)
  let pairFlat := flat.trans (alternatingTupleSplit h)
  obtain ⟨C, hC, hCA, hClower⟩ := alternating_haar_image_growing_sequence lie Exp chart hchart
    hzero a hm X words b₀ β cost b₁ b₂ pairFlat scale hscale rem hn p₀ hlim z₀ hs
    (fun r => ‖flat.symm.toContinuousLinearMap‖ * R r) (fun r => mul_nonneg (norm_nonneg _) (hR r))
    hRflat A (fun r => (hAc r).measurableSet) hAR hAlower
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCA] with r hr
  rintro y hy
  obtain ⟨x, ⟨u, hu, hxu⟩, hxy⟩ := hr hy
  refine ⟨u, hu, ?_⟩
  rw [← hxu] at hxy
  rw [← hxy]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  have he₁ : (pairFlat (f r u) j).1 =
      (exponentialBasisHomeomorph lie chart (b₁ r)).symm (u (Fin.castAdd h j)) := by
    change ((flat.trans (alternatingTupleSplit h))
      (flat.symm (exponentialTupleCoordinates lie chart (bs r) u)) j).1 = _
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      alternatingTupleSplit_apply]
    change (exponentialBasisHomeomorph lie chart (bs r (Fin.castAdd h j))).symm
      (u (Fin.castAdd h j)) = _
    simp only [bs, rescaledTupleBases, pairβ, pairCost, Fin.addCases_left, b₁]
  have he₂ : (pairFlat (f r u) j).2 =
      (exponentialBasisHomeomorph lie chart (b₂ r)).symm (u (Fin.natAdd h j)) := by
    change ((flat.trans (alternatingTupleSplit h))
      (flat.symm (exponentialTupleCoordinates lie chart (bs r) u)) j).2 = _
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
      alternatingTupleSplit_apply]
    change (exponentialBasisHomeomorph lie chart (bs r (Fin.natAdd h j))).symm
      (u (Fin.natAdd h j)) = _
    simp only [bs, rescaledTupleBases, pairβ, pairCost, Fin.addCases_right, b₂]
  rw [he₁, he₂, ← exponentialBasisHomeomorph_apply lie Exp chart hchart,
    ← exponentialBasisHomeomorph_apply lie Exp chart hchart,
    Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ChronologicalAlternatingHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The union-template Haar rate for actual chronological increments -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [Fintype I] in
theorem chronological_alternating_haar_image {m h c : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β β₁ β₂ : WordBasisSelections X words) (cost cost₁ cost₂ : words → ℝ)
    (flat : (Fin m → ℝ) ≃L[ℝ] (Fin (h + h) → Fin (finrank ℝ L) → ℝ))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (hn : 1 ≤ finrank ℝ L)
    (p₀ : AlternatingLawData (finrank ℝ L))
    (hlim : Tendsto (fun r =>
      let b := exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) (scale r)
      let b₁ := exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
        (fun j => cost₁ (β₁.val j)) (scale r)
      let b₂ := exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
        (fun j => cost₂ (β₂.val j)) (scale r)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ L) → ℝ) × (Fin (finrank ℝ L) → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p₀.1 p₀.2.1 p₀.2.2) z₀))
    (R : ℕ → ℝ) (hR : ∀ r, 0 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (S : ℕ → Set (Fin (h * 2) → G)) (hS : ∀ r, IsCompact (S r))
    (hbox₁ : ∀ r u, u ∈ S r → ∀ j : Fin h,
      u (finProdFinEquiv (j, (0 : Fin 2))) ∈ exponentialCoordinateBox (Exp ∘ lie)
        (exponentialRescaleBasis (WordBasisSelections.basis X words β₁)
          (fun i => cost₁ (β₁.val i)) (scale r)) (R r))
    (hbox₂ : ∀ r u, u ∈ S r → ∀ j : Fin h,
      u (finProdFinEquiv (j, (1 : Fin 2))) ∈ exponentialCoordinateBox (Exp ∘ lie)
        (exponentialRescaleBasis (WordBasisSelections.basis X words β₂)
          (fun i => cost₂ (β₂.val i)) (scale r)) (R r))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun r =>
      ((Measure.pi (fun _ : Fin (h * 2) =>
        Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume)) (S r)).toReal /
      Real.exp (scale r * ((h : ℝ) * columnBasisWeight cost₁ β₁.val +
        (h : ℝ) * columnBasisWeight cost₂ β₂.val)))) :
    ∃ C : ℕ → Set G, (∀ r, IsCompact (C r)) ∧
      (∀ᶠ r in atTop, C r ⊆ (fun u : Fin (h * 2) → G => (List.ofFn u).prod) '' S r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r =>
        ((Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume) (C r)).toReal /
          Real.exp (scale r * columnBasisWeight cost β.val)) := by
  let μ := Measure.map ((Exp ∘ lie) ∘ b₀.equivFun.symm) volume
  have he : ((Exp ∘ lie) ∘ b₀.equivFun.symm) = exponentialBasisHomeomorph lie chart b₀ := by
    funext x
    exact (exponentialBasisHomeomorph_apply lie Exp chart hchart b₀ x).symm
  let : SigmaFinite μ := by
    dsimp only [μ]
    rw [he]
    exact (exponentialBasisHomeomorph lie chart b₀).measurableEmbedding.sigmaFinite_map
  let B := fun r => alternatingWordBlockEquiv h '' S r
  have hB : ∀ r, IsCompact (B r) := fun r =>
    (hS r).image (continuous_alternatingWordBlockEquiv h)
  have hbox : ∀ r u, u ∈ B r → ∀ i, u i ∈ exponentialCoordinateBox (Exp ∘ lie)
      (rescaledTupleBases X words (Fin.addCases (fun _ => β₁) (fun _ => β₂))
        (Fin.addCases (fun _ => cost₁) (fun _ => cost₂)) (scale r) i) (R r) := by
    rintro r u ⟨v, hv, rfl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [alternatingWordBlockEquiv_left, rescaledTupleBases, Fin.addCases_left] using hbox₁ r v hv j
    · simpa only [alternatingWordBlockEquiv_right, rescaledTupleBases, Fin.addCases_right] using hbox₂ r v hv j
  have hmass (r : ℕ) : (Measure.pi fun _ : Fin (h + h) => μ) (B r) =
      (Measure.pi fun _ : Fin (h * 2) => μ) (S r) :=
    alternatingWordBlockEquiv_image_measure h μ (S r)
  dsimp only [μ] at hmass
  have hweight : (∑ i : Fin (h + h), columnBasisWeight
      (Fin.addCases (fun _ => cost₁) (fun _ => cost₂) i)
      ((Fin.addCases (motive := fun _ : Fin (h + h) => WordBasisSelections X words)
        (fun _ => β₁) (fun _ => β₂) i).val)) =
      (h : ℝ) * columnBasisWeight cost₁ β₁.val + (h : ℝ) * columnBasisWeight cost₂ β₂.val := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨C, hC, hCB, hClower⟩ := correlated_alternating_haar_image lie Exp chart hchart
    hzero a hm X words b₀ β β₁ β₂ cost cost₁ cost₂ flat scale hscale rem hn p₀ hlim z₀ hs
    R hR hRupper B hB hbox (by simpa only [hmass, hweight] using hlower)
  refine ⟨C, hC, ?_, hClower⟩
  filter_upwards [hCB] with r hr
  rintro y hy
  obtain ⟨u, ⟨v, hv, rfl⟩, he⟩ := hr hy
  exact ⟨v, hv, (alternatingWordBlockEquiv_prod h v).symm.trans he⟩

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

/-- The path-word subdivision prefactor is bounded by one fixed quadratic. -/
theorem coarse_path_word_prefactor_le {A r : ℝ} (hA : 0 ≤ A) (hr : 1 ≤ r) :
    3 + (A * r + 1) * (A * (1 + Real.log (2 + r)) + 2) ≤
      (3 + (A + 1) * (3 * A + 2)) * (1 + r) ^ 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hlog : 1 + Real.log (2 + r) ≤ 3 * r := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
    linarith
  have h1 : A * r + 1 ≤ (A + 1) * (1 + r) := by nlinarith
  have h2 : A * (1 + Real.log (2 + r)) + 2 ≤ (3 * A + 2) * (1 + r) := by
    have h := mul_le_mul_of_nonneg_left hlog hA
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  have hm := mul_le_mul h1 h2 (by positivity : 0 ≤ A * (1 + Real.log (2 + r)) + 2)
    (by positivity : 0 ≤ (A + 1) * (1 + r))
  calc
    _ ≤ 3 + (A + 1) * (1 + r) * ((3 * A + 2) * (1 + r)) := add_le_add le_rfl hm
    _ ≤ _ := by nlinarith [sq_nonneg r]

end PolycyclicRecognition

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactTupleThickening
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive compact thickening for finite factor tuples -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped Topology

/-- Continuity of factor multiplication supplies the positive compact cell
used to turn separated tuples into Haar volume. -/
theorem exists_small_factor_tuple_neighborhood
    {N D G : Type} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [TopologicalSpace D]
    [LocallyCompactSpace N] [LocallyCompactSpace D]
    [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
    [MetricSpace G] [IsTopologicalGroup G]
    (ι : N →* G) (κ : D →* G) (hι : Continuous ι) (hκ : Continuous κ)
    (μ : Measure N) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure]
    (h : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ U : Set ((Fin h → N) × (Fin h → D)), IsCompact U ∧
      ((Measure.pi fun _ : Fin h => μ).prod (Measure.pi fun _ : Fin h => ν)) U ≠ 0 ∧
      ∀ z ∈ U, dist (1 : Fin h → G) (fun i => ι (z.1 i) * κ (z.2 i)) < ρ / 2 := by
  let q : ((Fin h → N) × (Fin h → D)) → (Fin h → G) :=
    fun z i => ι (z.1 i) * κ (z.2 i)
  have hq : Continuous q := continuous_pi (fun i =>
    (hι.comp ((continuous_apply i).comp continuous_fst)).mul
      (hκ.comp ((continuous_apply i).comp continuous_snd)))
  have hopen : IsOpen {z | dist (1 : Fin h → G) (q z) < ρ / 2} :=
    isOpen_lt (continuous_const.dist hq) continuous_const
  have h1 : (1, 1) ∈ {z | dist (1 : Fin h → G) (q z) < ρ / 2} := by
    have he : q (1, 1) = 1 := by ext i; simp [q]
    simpa only [mem_ofPred_eq, he, dist_self] using half_pos hρ
  obtain ⟨U, hU, hU1, hsmall⟩ := exists_compact_subset hopen h1
  refine ⟨U, hU, ?_, hsmall⟩
  exact (Measure.measure_pos_of_nonempty_interior _ ⟨(1, 1), hU1⟩).ne'

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequencePathCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite terminal covers from the controlled-height path estimate -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology Pointwise

theorem exists_sequence_path_cover
    {G W : Type} [Group G] [MetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {K C b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (k : ℕ)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ S n,
      ∃ γ : Path (1 : G) x,
        PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          η * scale n + b * (1 + Real.log (2 + scale n)))
    (hupper : ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∃ t : ℕ → Finset G, (∀ n, (↑(t n) : Set G) ⊆ S n) ∧
      (∀ n, ∀ x ∈ S n, ∃ y ∈ t n, dist x y ≤ 1) ∧
      ∀ ε : ℝ, 0 < ε → HasSubexponentialUpperBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * P (E + closedBall 0 ε))) := by
  choose t ht hsep hcover using fun n =>
    exists_separated_net_of_totallyBounded (hS n) zero_lt_one
  refine ⟨t, ht, hcover, ?_⟩
  intro ε hε
  let H := 3 + (C + 1) * (3 * C + 2)
  have hH : 0 < H := by dsimp [H] <;> positivity
  have hpoly := (subexponential_upper_polynomial (mul_pos hD (pow_pos hH k)) (2 * k)).along_sequence hs
  have hbound : ∀ᶠ n in atTop,
      ((t n).card : ℝ) / Real.exp (scale n * P (E + closedBall 0 ε)) ≤
        (D * H ^ k) * (1 + scale n) ^ (2 * k) := by
    filter_upwards [hpaths (ε / 2) (half_pos hε), hs.eventually (eventually_ge_atTop (1 : ℝ)),
      hs.eventually (eventually_logarithmic_error_le (K * C + b) (2 * K) (half_pos hε))]
      with n hp hn herr
    have hr : 0 < scale n := by linarith
    have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
      have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith)
      linarith
    have he : K * (C * (1 + Real.log (2 + scale n)) + 2) +
        (ε / 2 * scale n + b * (1 + Real.log (2 + scale n))) ≤ scale n * ε := by
      nlinarith
    have hc := hupper hr (mul_nonneg hC hr.le) (mul_nonneg hC hlog) hε.le he (t n)
      (fun x hx y hy hxy => (hsep n x hx y hy hxy).le)
      (fun x hx => hp x (ht n hx))
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    apply hc.trans
    have hf := coarse_path_word_prefactor_le hC hn
    calc
      D * (3 + (C * scale n + 1) * (C * (1 + Real.log (2 + scale n)) + 2)) ^ k * _ ≤
          D * (H * (1 + scale n) ^ 2) ^ k * Real.exp (scale n * P (E + closedBall 0 ε)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact pow_le_pow_left₀ (by positivity) hf k
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  intro δ hδ
  filter_upwards [hbound, hpoly δ hδ] with n hb hp
  exact hb.trans hp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceQuotientVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient log boxes in the chosen Haar normalization

The quotient Jacobian and the packing argument use the same Haar measure.
Uniqueness of Haar measure transfers the exponential cube formula to that
normalization, including along an arbitrary sequence of profile scales.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology ENNReal NNReal

variable {E Q L : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] [LieRing L] [LieAlgebra ℝ L]

/-- The logarithmic cube formula for any actual Lie-algebra model and any
Haar normalization. The constant is independent of the cube radius. -/
theorem haar_model_cube_volume
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ R : ℝ, 0 ≤ R →
      μ (exponentialCoordinateBox (Exp ∘ e) b R) =
        (c : ℝ≥0∞) * ENNReal.ofReal (2 * R) ^ n := by
  let : IsTopologicalGroup Q := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨chart, ν, _, hν, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp
    (e.nilpotent_iff_equiv_nilpotent.mp hnil) (b.map e.toLinearEquiv)
  let coordinates : (Fin n → ℝ) ≃ₜ Q :=
    (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  let : LocallyCompactSpace Q := coordinates.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology Q := coordinates.symm.secondCountableTopology
  have : ν.IsHaarMeasure := hν
  have hbox (R : ℝ) : exponentialCoordinateBox (Exp ∘ e) b R =
      exponentialCoordinateBox Exp (b.map e.toLinearEquiv) R := by
    ext q
    constructor
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e v, rfl, ?_⟩
      change ‖(b.map e.toLinearEquiv).equivFun (e.toLinearEquiv v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply,
        LinearEquiv.symm_apply_apply] using hv
    · rintro ⟨v, rfl, hv⟩
      refine ⟨e.symm v, by simp, ?_⟩
      change ‖b.equivFun (e.toLinearEquiv.symm v)‖ ≤ R
      simpa only [Basis.map_equivFun, LinearEquiv.trans_apply] using hv
  refine ⟨Measure.haarScalarFactor μ ν, Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν,
    ?_⟩
  intro R hR
  rw [hbox]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [Measure.smul_apply, hvol R hR]
  rfl

/-- Subexponential radii have finite, subexponential Haar volume in the
normalization already used for the quotient action. -/
theorem haar_model_sequence_boxes
    (haar : NilpotentExponentialHaarInput E Q)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q) (hnil : LieRing.IsNilpotent L)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (μ : Measure Q) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ j, 0 ≤ R j) (hR : HasSubexponentialUpperBoundSeq scale R) :
    (∀ j, μ (exponentialCoordinateBox (Exp ∘ e) b (R j)) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun j =>
        (μ (exponentialCoordinateBox (Exp ∘ e) b (R j))).toReal) := by
  obtain ⟨c, _, hvol⟩ := haar_model_cube_volume haar Exp hExp e hnil b μ
  have htwo := (sequence_subexponential_upper_const hs 2).mul hR
    (Eventually.of_forall (fun _ => by norm_num))
  have hp := htwo.pow hs
    (Eventually.of_forall (fun j => mul_nonneg (by norm_num) (hR0 j))) n
  have hc := (sequence_subexponential_upper_const hs (c : ℝ)).mul hp
    (Eventually.of_forall (fun _ => c.coe_nonneg))
  constructor
  · intro j
    rw [hvol _ (hR0 j)]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · intro ε hε
    filter_upwards [hc ε hε] with j hj
    rw [hvol _ (hR0 j), ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal
        (mul_nonneg (by norm_num) (hR0 j))]
    exact hj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceTupleVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume rates in the endpoint-tuple projection

A fixed positive thickening cell and subexponential auxiliary volume
preserve the exponential lower rate of the number of separated tuples.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

theorem tuple_region_volume_subexponential
    {D : Type} [MeasurableSpace D] (ν : Measure D) [SigmaFinite ν]
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (B : ℕ → Set D) (hBfinite : ∀ n, ν (B n) ≠ ⊤)
    (hB : HasSubexponentialUpperBoundSeq scale (fun n => (ν (B n)).toReal)) (h : ℕ) :
    let Q := fun n => {d : Fin h → D | ∀ i, d i ∈ B n}
    (∀ n, (Measure.pi fun _ : Fin h => ν) (Q n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale
        (fun n => ((Measure.pi fun _ : Fin h => ν) (Q n)).toReal) := by
  have hvol (n : ℕ) : (Measure.pi fun _ : Fin h => ν)
      {d : Fin h → D | ∀ i, d i ∈ B n} = (ν (B n)) ^ h := by
    have he : {d : Fin h → D | ∀ i, d i ∈ B n} = Set.pi univ (fun _ => B n) := by
      ext d
      simp
    rw [he, Measure.pi_pi]
    simp
  constructor
  · intro n
    rw [hvol]
    exact ENNReal.pow_ne_top (hBfinite n)
  · simpa only [hvol, ENNReal.toReal_pow] using
      hB.pow hs (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) h

theorem lower_volume_rate_of_tuple_count
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (N : ℕ → ℕ) (A B : ℕ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcfinite : c ≠ ⊤)
    (hAfinite : ∀ n, A n ≠ ⊤) (hBfinite : ∀ n, B n ≠ ⊤)
    (hB : HasSubexponentialUpperBoundSeq scale (fun n => (B n).toReal))
    {p : ℝ}
    (hN : HasSubexponentialLowerBoundSeq scale
      (fun n => (N n : ℝ) / Real.exp (scale n * p)))
    (hbound : ∀ n, (N n : ℝ≥0∞) * c ≤ A n * B n) :
    HasSubexponentialLowerBoundSeq scale (fun n => (A n).toReal / Real.exp (scale n * p)) := by
  have hc := sequence_subexponential_lower_const hs (ENNReal.toReal_pos hc0 hcfinite)
  have hden := hB.add (sequence_subexponential_upper_const hs 1) hs
  apply ((hN.mul hc).div hden
    (Eventually.of_forall (fun n => by positivity))).mono
  apply Eventually.of_forall
  intro n
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (hAfinite n) (hBfinite n)) (hbound n)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hb
  apply (div_le_iff₀ (show 0 < (B n).toReal + 1 by positivity)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr
  have hA0 : 0 ≤ (A n).toReal := ENNReal.toReal_nonneg
  nlinarith

end PolycyclicRecognition

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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_1_r7f7c7b_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r7f7c7b_1 : Nontrivial (rootSpace H χ) :=
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
local instance instNontrivialSubtypeMemLieSubmoduleRealLieSubalgebraRootSpaceCoeWeight_solutions_2_r7f7c7b_2 : Nontrivial (rootSpace H χ) :=
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAlternatingComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing an alternating target product with the terminal cover

The product-image theorem is applied to the correlated increment set itself.
Its terminal lifts then give a volume comparison in the original Lie group.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
theorem alternating_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (I : ℕ → Set (Fin (h * 2) → F.N.carrier)) (hIc : ∀ n, IsCompact (I n))
    (hbox₁ : ∀ n u, u ∈ I n → ∀ j : Fin h,
      u (finProdFinEquiv (j, (0 : Fin 2))) ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E₁ β₁ (scale n) (R n))
    (hbox₂ : ∀ n u, u ∈ I n → ∀ j : Fin h,
      u (finProdFinEquiv (j, (1 : Fin 2))) ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E₂ β₂ (scale n) (R n))
    (hvol : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi fun _ : Fin (h * 2) =>
        Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume) (I n)).toReal /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (s : ℕ → Finset (Fin (h * 2) → G))
    (p : ℕ → (Fin (h * 2) → G) → (Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))
    (U : Set ((Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))) (hU : IsCompact U)
    (t : ℕ → Finset G) {ρ Rc q : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin (h * 2) → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hI : ∀ n u, u ∈ I n → ∃ x ∈ s n, ∃ z ∈ U,
      prefixCoordinateEquiv (h * 2) u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  obtain ⟨C, _, hCI, hClower⟩ := chronological_alternating_haar_image F.N.equiv F.ExpN
    chartN hchartN F.isExpN.map_zero aN hm M.letter M.wordList b₀ β β₁ β₂
    (M.boxCost T hunimod eW E) (M.boxCost T hunimod eW E₁) (M.boxCost T hunimod eW E₂)
    (bundleOutputChart (h + h) _) scale hs rem hn p₀ hlim z₀ hsub R hR0 hR I hIc hbox₁ hbox₂ hvol
  exact M.terminal_product_exponent_le T F hunimod eW hExpG hinjG realize π hπ hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN μ b₀ β (by omega)
    scale RH η hs hscale hRH0 hRH hη s p U hU I C t hp hsmall hd hhgt hI hCI hClower hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanLogRegionVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Cartan log restriction has subexponential Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D] [SimplyConnectedSpace D]
  [MeasurableSpace D] [BorelSpace D]

set_option maxHeartbeats 1000000 in
/-- The coordinate restriction produced by the actual path lifts is an
exponential box. Its volume is finite and subexponential in any Haar
normalization, with no separate volume hypothesis. -/
theorem cartan_log_regions_volume
    (haar : NilpotentExponentialHaarInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (e : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) D) (hbij : Function.Bijective Exp)
    (μ : Measure D) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) := by
  have hnil : LieRing.IsNilpotent H := by infer_instance
  have hbox (n : ℕ) :
      {d : D | ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij d)‖ ≤ R n} =
        exponentialCoordinateBox (Exp ∘ e) (finBasis ℝ H) (R n) := by
    ext d
    constructor
    · intro hd
      exact ⟨cartanLog H e Exp hbij d, exp_cartanLog H e Exp hbij d, hd⟩
    · rintro ⟨v, rfl, hv⟩
      change ‖(finBasis ℝ H).equivFun (cartanLog H e Exp hbij (Exp (e v)))‖ ≤ R n
      rw [cartanLog_exp]
      exact hv
  simpa only [hbox] using
    haar_model_sequence_boxes haar Exp hExp e hnil (finBasis ℝ H) μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorLogVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The log-region volume theorem for the actual Cartan factor -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem CartanFactorModel.log_regions_volume
    (haar : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbij : Function.Bijective F.ExpD)
    (μ : Measure F.D.carrier) [μ.IsHaarMeasure]
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    let B := fun n => {d : F.D.carrier |
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbij d)‖ ≤ R n}
    (∀ n, μ (B n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (μ (B n)).toReal) :=
  cartan_log_regions_volume (L := GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (E := F.D.modelSpace) (D := F.D.carrier) H haar F.ExpD F.isExpD
    F.D.equiv hbij μ scale R hs hR0 hR

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSeparatedAlternatingComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated target tuples supply the alternating increment volume

The auxiliary Cartan volume is subexponential. Thus the finite separated
count supplies the full correlated Haar lower bound needed by the product
comparison; this lower bound is not assumed independently.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
theorem separated_alternating_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (p : ℕ → (Fin (h * 2) → G) → (Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))
    (U : Set ((Fin (h * 2) → F.N.carrier) × (Fin (h * 2) → F.D.carrier))) (hU : IsCompact U)
    (hUpos : ((Measure.pi fun _ : Fin (h * 2) =>
      Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume).prod
        (Measure.pi fun _ : Fin (h * 2) => ν)) U ≠ 0)
    (t : ℕ → Finset G) {ρ Rc q : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin (h * 2) → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ / 2)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → ρ ≤ dist x y)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hinc : ∀ n x, x ∈ s n → ∀ i, (prefixCoordinateEquiv (h * 2)).symm (p n x).1 i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (alternatingCoordinateFamily h E₁ E₂ i) (alternatingCoordinateFamily h β₁ β₂ i)
        (scale n) (R n))
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : SigmaFinite μ := inferInstance
  have hEc (i : Fin (h * 2)) : IsCompact (alternatingCoordinateFamily h E₁ E₂ i) := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hE0 (i : Fin (h * 2)) : (0 : W) ∈ alternatingCoordinateFamily h E₁ E₂ i := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hβ (i : Fin (h * 2)) : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (alternatingCoordinateFamily h E₁ E₂ i))
      (alternatingCoordinateFamily h β₁ β₂ i).val := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  obtain ⟨Q, RD, hQ0, hQ, hRD0, hRD, hex⟩ := M.exists_controlled_increment_volume T F hunimod eW
    hExpG realize chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD μ ν b₀ β
    (h * 2) (alternatingCoordinateFamily h E₁ E₂) hEc hE0 (alternatingCoordinateFamily h β₁ β₂) hβ
    scale RH R η hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη s p U hU hp hsmall hsep hd hhgt hinc
  choose I hIc hIm hmass hbox hreach using hex
  obtain ⟨RQ, hRQ0, hRQ, hQle⟩ := finite_subexponential_envelope hs Q hQ0 hQ
  obtain ⟨hDfinite, hDvol⟩ := F.log_regions_volume haarD hbijD ν scale RD hs hRD0 hRD
  obtain ⟨hDpiFinite, hDpiVol⟩ := tuple_region_volume_subexponential ν hs _ hDfinite hDvol (h * 2)
  have hIlower := lower_volume_rate_of_tuple_count hs (fun n => (s n).card)
    (fun n => (Measure.pi fun _ : Fin (h * 2) => μ) (I n))
    (fun n => (Measure.pi fun _ : Fin (h * 2) => ν)
      {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n})
    (((Measure.pi fun _ : Fin (h * 2) => μ).prod (Measure.pi fun _ : Fin (h * 2) => ν)) U)
    hUpos hU.measure_lt_top.ne (fun n => (hIc n).measure_lt_top.ne) hDpiFinite hDpiVol hnum hmass
  have hbox' (n : ℕ) (u : Fin (h * 2) → F.N.carrier) (hu : u ∈ I n) (i : Fin (h * 2)) :
      u i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (alternatingCoordinateFamily h E₁ E₂ i) (alternatingCoordinateFamily h β₁ β₂ i)
        (scale n) (RQ n) := by
    obtain ⟨v, hv, hb⟩ := hbox n u hu i
    exact ⟨v, hv, hb.trans (hQle i n)⟩
  exact M.alternating_product_exponent_le T F hunimod eW hExpG hinjG realize rem π hπ hπExp
    chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN b₀ β β₁ β₂ E E₁ E₂
    hh aN hm hn scale RH RQ η hs hscale hRH0 hRQ0 hRH hRQ hη p₀ hlim z₀ hsub I hIc
    (fun n u hu j => by
      simpa only [alternatingCoordinateFamily_left] using hbox' n u hu (finProdFinEquiv (j, (0 : Fin 2))))
    (fun n u hu j => by
      simpa only [alternatingCoordinateFamily_right] using hbox' n u hu (finProdFinEquiv (j, (1 : Fin 2))))
    hIlower s p U hU t hp hsmall hd hhgt hreach hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPathAlternatingComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Alternating volume comparison from actual controlled target paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
theorem path_alternating_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (t : ℕ → Finset G) {Rc q : ℝ}
    (hpaths : ∀ n x, x ∈ s n →
      ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
          ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
        (∀ i, PathMetricBound (path i) (A * scale n)
          (B * (1 + Real.log (2 + scale n)))) ∧
        (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
          ‖(π (path i u)).toAdd - scale n • z‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
        ∀ i : Fin (h * 2),
          ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
            η n * scale n)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩) y ≤ Rc)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * q))) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤ q := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let path := fun n (x : Fin (h * 2) → G) =>
    if hx : x ∈ s n then (hpaths n x hx).choose
    else fun i : Fin (h * 2) => (exists_short_path_of_minimizing_paths hpath 1
      ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).choose
  have hmetric n x (hx : x ∈ s n) i : PathMetricBound (path n x i)
      (A * scale n) (B * (1 + Real.log (2 + scale n))) := by
    simpa only [path, dite_eq_left hx] using (hpaths n x hx).choose_spec.1 i
  have htemplate n x (hx : x ∈ s n) i u : ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
      ‖(π (path n x i u)).toAdd - scale n • z‖ ≤
        2 * scale n * η n + A * (1 + Real.log (2 + scale n)) := by
    simpa only [path, dite_eq_left hx] using (hpaths n x hx).choose_spec.2.1 i u
  have hend n x (hx : x ∈ s n) (i : Fin (h * 2)) :
      ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
        η n * scale n := (hpaths n x hx).choose_spec.2.2 i
  have hEc (i : Fin (h * 2)) : IsCompact (alternatingCoordinateFamily h E₁ E₂ i) := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hEn (i : Fin (h * 2)) : (alternatingCoordinateFamily h E₁ E₂ i).Nonempty := by
    refine ⟨0, ?_⟩
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  have hβ (i : Fin (h * 2)) : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (alternatingCoordinateFamily h E₁ E₂ i))
      (alternatingCoordinateFamily h β₁ β₂ i).val := by
    unfold alternatingCoordinateFamily
    split_ifs <;> assumption
  obtain ⟨RH, R, p, hRH0, hR0, hRH, hR, hp⟩ := M.exists_sequence_path_tuple_lifts
    T F hunimod eW hExpG realize π hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD b₀ β hpath hKπ hLip (h * 2) (alternatingCoordinateFamily h E₁ E₂)
    (alternatingCoordinateFamily h β₁ β₂) hEc hEn hβ scale η hs hscale hη0 hη
    A B hA hB (fun n => (↑(s n) : Set (Fin (h * 2) → G))) path hmetric htemplate hend
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : SigmaFinite μ := inferInstance
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨U, hU, hUpos, hsmall⟩ := exists_small_factor_tuple_neighborhood
    F.inclusionN F.inclusionD F.closedN.continuous F.closedD.continuous μ ν (h * 2)
    (show (0 : ℝ) < 1 by norm_num)
  have hη' : Tendsto (fun n => ((h * 2 : ℕ) : ℝ) * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hη
  exact M.separated_alternating_product_exponent_le T F hunimod eW hExpG hinjG realize rem
    π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD
    b₀ β β₁ β₂ E E₁ E₂ hh aN hm hn scale RH R (fun n => ((h * 2 : ℕ) : ℝ) * η n)
    hs (fun n => lt_of_lt_of_le zero_lt_one (hscale n)) hRH0 hR0 hRH hR hη' p₀ hlim z₀ hsub
    hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν s p U hU hUpos t
    (fun n x hx => (hp n x hx).1) hsmall hsep
    (fun n x hx => (hp n x hx).2.1) (fun n x hx => (hp n x hx).2.2.1)
    (fun n x hx => (hp n x hx).2.2.2) hnum hcover hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceTerminalCover
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPairAction _root_.OAI.PolycyclicRecognition.normalizedPairContinuousAction _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Source terminal covers transported through the normalized quasi-isometry -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold ENNReal NNReal Pointwise Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)


set_option maxHeartbeats 1000000 in
include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
theorem exists_normalized_source_terminal_cover
    [SimplyConnectedSpace G] [ProperSpace G]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ≥0} (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {C b : ℝ} (hC : 0 ≤ C)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ S n,
      ∃ γ : Path (1 : G) x,
        PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          η * scale n + b * (1 + Real.log (2 + scale n)))
    {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G) :
    ∃ t : ℕ → Finset G,
      (∀ n, ∀ x ∈ S n, ∃ y ∈ t n, dist ((p n).val.1 (base n * x)) y ≤ Λ) ∧
      ∀ ε : ℝ, 0 < ε → HasSubexponentialUpperBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n *
          (M.supportIn T hunimod eW).templateSupport (E + closedBall 0 ε))) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨D, k, hD, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ γ₀ zero_lt_one
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize hbijN hbijD dynkinN d)
    hpath Kπ.coe_nonneg (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
  obtain ⟨u, _, hcover, hrate⟩ := exists_sequence_path_cover scale hs π E
    (M.supportIn T hunimod eW).templateSupport S hS hC hD k hpaths (hupper hE hne)
  let t := fun n => (u n).image (fun x => (p n).val.1 (base n * x))
  refine ⟨t, ?_, ?_⟩
  · intro n x hx
    obtain ⟨y, hy, hxy⟩ := hcover n x hx
    refine ⟨(p n).val.1 (base n * y), Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    calc
      _ ≤ Λ * dist (base n * x) (base n * y) := (p n).property.1.1.dist_le_mul _ _
      _ = Λ * dist x y := by rw [dist_mul_left]
      _ ≤ Λ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hxy Λ.coe_nonneg
  · intro ε hε δ hδ
    filter_upwards [hrate ε hε δ hδ] with n hn
    apply le_trans _ hn
    apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast Finset.card_image_le

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceTargetComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing target multiplication with actual source terminal paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
  [IsTopologicalGroup F.D.carrier]

set_option maxHeartbeats 1000000 in
theorem source_target_product_exponent_le_m_oai
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (rem : RemezPolynomialInput)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
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
    (β β₁ β₂ : M.Bases) (E E₁ E₂ : Set W)
    {h cN : ℕ} (hh : 0 < h) (aN : DynkinCoefficients cN 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (hn : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p₀ : AlternatingLawData (finrank ℝ (cartanRootIdeal H)))
    (hlim : Tendsto (fun n =>
      let b := M.boxBasis T hunimod eW E β (scale n)
      let b₁ := M.boxBasis T hunimod eW E₁ β₁ (scale n)
      let b₂ := M.boxBasis T hunimod eW E₂ β₂ (scale n)
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂)) atTop (𝓝 p₀))
    (z₀ : Fin h → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ×
      (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
    (hsub : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct aN p₀.1 p₀.2.1 p₀.2.2) z₀))
    (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂) (h01 : (0 : W) ∈ E₁) (h02 : (0 : W) ∈ E₂)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hβ₂ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₂) β₂.val)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure] [SigmaFinite ν]
    (s : ℕ → Finset (Fin (h * 2) → G))
    (htarget : ∀ᶠ n in atTop, ∀ x, x ∈ s n →
      ∃ path : ∀ i : Fin (h * 2), Path (1 : G)
          ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)),
        (∀ i, PathMetricBound (path i) (A * scale n)
          (B * (1 + Real.log (2 + scale n)))) ∧
        (∀ i u, ∃ z ∈ alternatingCoordinateFamily h E₁ E₂ i,
          ‖(π (path i u)).toAdd - scale n • z‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ∧
        ∀ i : Fin (h * 2),
          ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
            η n * scale n)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → 1 ≤ dist x y)
    (hnum : HasSubexponentialLowerBoundSeq scale (fun n => ((s n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))))
    (Esrc : Set W) (hEsrc : IsCompact Esrc) (hne : Esrc.Nonempty)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {Cs bs : ℝ} (hCs : 0 ≤ Cs)
    (hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ S n,
      ∃ path : Path (1 : G) z,
        PathMetricBound path (Cs * scale n) (Cs * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ Esrc, ‖(π (path t)).toAdd - scale n • w‖ ≤
          ε * scale n + bs * (1 + Real.log (2 + scale n)))
    {Λ : ℝ≥0} (p : ℕ → NormalizedPair G Λ) (base : ℕ → G)
    (hterminal : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ z ∈ S n,
      x ⟨h * 2 - 1, Nat.sub_lt (by omega) (by decide)⟩ = (p n).val.1 (base n * z)) :
    columnBasisWeight (M.boxCost T hunimod eW E) β.val ≤
      (M.supportIn T hunimod eW).templateSupport Esrc := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp htarget
  let s' : ℕ → Finset (Fin (h * 2) → G) := fun n => if N ≤ n then s n else ∅
  have hsub' (n : ℕ) : s' n ⊆ s n := by
    dsimp only [s']
    split_ifs <;> simp
  have hpaths' n x (hx : x ∈ s' n) := by
    have hn : N ≤ n := by
      by_contra hn
      simp only [s', ite_eq_right hn, Finset.notMem_empty] at hx
    exact hN n hn x (hsub' n hx)
  have hnum' : HasSubexponentialLowerBoundSeq scale (fun n => ((s' n).card : ℝ) /
      Real.exp (scale n * ((h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₁) β₁.val +
        (h : ℝ) * columnBasisWeight (M.boxCost T hunimod eW E₂) β₂.val))) := by
    intro ε hε
    filter_upwards [hnum ε hε, eventually_ge_atTop N] with n hn hlarge
    simpa only [s', ite_eq_left hlarge] using hn
  obtain ⟨t, hcover, hcount⟩ := M.exists_normalized_source_terminal_cover T F hunimod eW π
    hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExpG realize b₀ β
    hpath hLip hEsrc hne scale hs S hS hCs hsource p base
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings hEsrc hne
  intro ε hε
  apply M.path_alternating_product_exponent_le (Rc := (Λ : ℝ)) T F hunimod eW hExpG hinjG realize rem
    π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD dynkinN dynkinD haarN haarD
    b₀ β β₁ β₂ E E₁ E₂ hh aN hm hn scale η hs hscale hη0 hη hpath Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
    A B hA hB p₀ hlim z₀ hsub hE₁ hE₂ h01 h02 hβ₁ hβ₂ ν s' t hpaths' (fun n x hx y hy => hsep n x (hsub' n hx) y (hsub' n hy)) hnum' ?_
    (hcount ε hε)
  filter_upwards [hterminal] with n hn
  intro x hx
  obtain ⟨z, hz, he⟩ := hn x (hsub' n hx)
  obtain ⟨y, hy, hd⟩ := hcover n z hz
  refine ⟨y, hy, ?_⟩
  rw [he]
  exact hd

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le_m_oai
