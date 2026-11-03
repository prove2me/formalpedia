-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:30:35.787233+00:00
-- url     : https://prove2.me/submissions/ef366e1b-a530-4ed3-b588-80317e24ecb2

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D006
import Definitions.Def_OAIQ093D015
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_templateSupport_le_of_recurrent_segment_cells_sequence_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ParametricLieWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie words as functions of their structure constants

The bilinear bracket itself varies in a finite-dimensional vector space.
Word evaluation is smooth jointly in that bracket and the input vectors, so
word identities and normalization equations persist under limits.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bound on bilinear evaluations bounds the iterated operator norm. -/
theorem norm_bilinear_le_of_bound (B : V →L[ℝ] V →L[ℝ] V) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound B hC
  intro x
  apply ContinuousLinearMap.opNorm_le_bound (B x) (mul_nonneg hC (norm_nonneg x))
  exact h x

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞}

/-- Alternation and Jacobi are closed conditions on the bracket. -/
theorem isClosed_setOf_isLieBracket :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | IsLieBracket B} := by
  simp only [IsLieBracket, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq (by fun_prop) (by fun_prop)

/-- A fixed word equation is closed even while both bracket and generators
vary. This is the normalization condition used by rescaled word bases. -/
theorem isClosed_bilinearWord_eq [Fintype I] (w : FreeMagma I) (v : V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      evalBilinearWord p.1 p.2 w = v} := by
  have hc : Continuous (fun p : (V →L[ℝ] V →L[ℝ] V) × (I → V) =>
      evalBilinearWord p.1 p.2 w) :=
    (contDiff_evalBilinearWord (n := 0) Prod.fst (fun p => p.2) contDiff_fst
      (fun i => (contDiff_apply ℝ V i).comp contDiff_snd) w).continuous
  exact isClosed_eq hc continuous_const

/-- All finite word-normalization equations hold on a closed parameter set. -/
theorem isClosed_wordNormalizations [Fintype I] {J : Type}
    (w : J → FreeMagma I) (v : J → V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      ∀ j, evalBilinearWord p.1 p.2 (w j) = v j} := by
  simp only [ofPred_forall]
  exact isClosed_iInter (fun j => isClosed_bilinearWord_eq (w j) (v j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactLieLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact families of normalized Lie laws

Bounded brackets and generators satisfying fixed word-basis identities form
a compact parameter set. Limits retain the Lie identities and the exact word
normalizations, so bracket generation cannot disappear in a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {V I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ V] [Fintype I]

/-- The exact word identities are closed, while the coefficient and
letter bounds give a compact ambient set. -/
theorem isCompact_normalizedLieParameters
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedLieParameters w b C) := by
  let : FiniteDimensional ℝ (V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (V →L[ℝ] V →L[ℝ] V) := ContinuousLinearMap.finiteDimensional
  let : PseudoMetricSpace (V →L[ℝ] V →L[ℝ] V) :=
    (inferInstance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V)).toPseudoMetricSpace
  let : ProperSpace (V →L[ℝ] V →L[ℝ] V) := FiniteDimensional.proper ℝ _
  let : ProperSpace (I → V) := FiniteDimensional.proper ℝ _
  have hc : IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) | IsLieBracket p.1} :=
    isClosed_setOf_isLieBracket.preimage continuous_fst
  have hw := isClosed_wordNormalizations w b
  have he : normalizedLieParameters w b C =
      (closedBall (0 : V →L[ℝ] V →L[ℝ] V) C ×ˢ closedBall (0 : I → V) C) ∩
        {p | IsLieBracket p.1 ∧ ∀ j, evalBilinearWord p.1 p.2 (w j) = b j} := by
    ext p
    simp only [normalizedLieParameters, mem_ofPred_eq, mem_inter_iff, mem_prod,
      mem_closedBall, dist_eq_norm, sub_zero]
    tauto
  rw [he]
  exact (isCompact_closedBall _ _ |>.prod (isCompact_closedBall _ _)).inter_right (hc.inter hw)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generation persists in the compact normalized family

The word-normalization equations express a fixed vector-space basis as words
in the generators. They therefore imply Lie generation for every limiting law.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recursively evaluated operation agrees with the Lie structure that
it defines. -/
theorem evalBilinearWord_eq_lieWord (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (w : FreeMagma I) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    evalBilinearWord B X w = evalBracketWord X w := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => change B _ _ = B _ _; rw [ha, hb]

/-- Fixed basis-word identities prevent loss of generation in a limit. -/
theorem lieSpan_eq_top_of_word_basis (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    LieSubalgebra.lieSpan ℝ V (Set.range X) = ⊤ := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  have hb (j : J) : b j ∈ LieSubalgebra.lieSpan ℝ V (Set.range X) := by
    rw [← hw j, evalBilinearWord_eq_lieWord B h]
    exact evalBracketWord_mem_lieSpan X (w j)
  have hspan : (⊤ : Submodule ℝ V) ≤
      (LieSubalgebra.lieSpan ℝ V (Set.range X)).toSubmodule := by
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)
  apply top_unique
  intro v _
  exact hspan (Submodule.mem_top)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BilinearGeneratorOrbit
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generator adjoint orbits in a fixed coordinate norm

This is the coordinate version of the spanning argument. Its exponential
operators use the fixed norm on the parameter space, so they vary
continuously with the bilinear bracket, including at limiting laws.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem bilinear_generator_mem_orbitSpan (B : V →L[ℝ] V →L[ℝ] V)
    (X : I → V) (i : I) : X i ∈ bilinearOrbitSpan B X := by
  apply Submodule.subset_span
  exact ⟨([], i), rfl⟩

omit [FiniteDimensional ℝ V] in
theorem bilinear_exp_mem_orbitSpan (B : V →L[ℝ] V →L[ℝ] V)
    (X : I → V) (i : I) (t : ℝ) {v : V}
    (hv : v ∈ bilinearOrbitSpan B X) :
    NormedSpace.exp (t • B (X i)) v ∈ bilinearOrbitSpan B X := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨w, j⟩, rfl⟩ := hv
    apply Submodule.subset_span
    exact ⟨((i, t) :: w, j), rfl⟩
  | zero => simp
  | add v u _ _ hv hu => simpa using (bilinearOrbitSpan B X).add_mem hv hu
  | smul c v _ hv => simpa using (bilinearOrbitSpan B X).smul_mem c hv

/-- Differentiating the fixed-norm adjoint exponential stays in its closed
orbit span. -/
theorem bilinear_ad_mem_orbitSpan (B : V →L[ℝ] V →L[ℝ] V)
    (X : I → V) (i : I) {v : V} (hv : v ∈ bilinearOrbitSpan B X) :
    B (X i) v ∈ bilinearOrbitSpan B X := by
  let f : ℝ → V := fun t => NormedSpace.exp (t • B (X i)) v
  have hd : HasDerivAt f (B (X i) v) 0 := by
    simpa [f] using (hasDerivAt_exp_smul_const (B (X i)) (0 : ℝ)).clm_apply
      (hasDerivAt_const (0 : ℝ) v)
  have h := range_deriv_subset_closure_span_image f dense_univ (Set.mem_range_self 0)
  rw [hd.deriv] at h
  have hs : Submodule.span ℝ (f '' Set.univ) ≤ bilinearOrbitSpan B X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, _, rfl⟩
    exact bilinear_exp_mem_orbitSpan B X i t hv
  exact closure_minimal hs (bilinearOrbitSpan B X).closed_of_finiteDimensional h

/-- Exact word-basis normalization implies spanning by the coordinate
adjoint orbits, for every law in the compact family. -/
theorem bilinearOrbitSpan_eq_top {J : Type}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j) :
    bilinearOrbitSpan B X = ⊤ := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  have hX := lieSpan_eq_top_of_word_basis B hB X b w hw
  let U := bilinearOrbitSpan B X
  have hstab : submoduleAdjointStabilizer U = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩ v hv
    exact bilinear_ad_mem_orbitSpan B X i hv
  let K : LieSubalgebra ℝ V := { U with
    lie_mem' := by
      intro x y hx hy
      have hx' : x ∈ submoduleAdjointStabilizer U := by rw [hstab]; trivial
      exact hx' y hy }
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact bilinear_generator_mem_orbitSpan B X i
  exact congrArg LieSubalgebra.toSubmodule hK

/-- A finite basis of fixed-norm adjoint words can be selected at each
limiting law. This is the nondegeneracy used by the uniform-chart argument. -/
theorem exists_bilinearOrbit_basis {J : Type}
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V)
      (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I),
      ∀ k, bilinearAdjointWord B X (w k) (X (i k)) = b k := by
  classical
  have hspan : ⊤ ≤ bilinearOrbitSpan B X :=
    (bilinearOrbitSpan_eq_top B hB X b₀ w₀ hw₀).ge
  let J' := (linearIndepOn_empty ℝ (id : V → V)).extend
    (Set.empty_subset (Set.range (fun p : List (I × ℝ) × I =>
      bilinearAdjointWord B X p.1 (X p.2))))
  let b : Basis J' ℝ V := Basis.ofSpan hspan
  let : Fintype J' := Fintype.ofFinite _
  let e : J' ≃ Fin (finrank ℝ V) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have hb (k : Fin (finrank ℝ V)) : ∃ p : List (I × ℝ) × I,
      bilinearAdjointWord B X p.1 (X p.2) = (b.reindex e) k := by
    simpa only [Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ Set.range b from ⟨_, rfl⟩))
  choose p hp using hb
  exact ⟨b.reindex e, fun k => (p k).1, fun k => (p k).2, hp⟩

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bracket bounds from finitely many structure constants

The norm is the coordinate maximum in a specified basis. Consequently the
bound applies uniformly to every rescaled word basis from the box calculus.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- Bounding the finitely many basis brackets bounds the full bracket as a
bilinear map, in the coordinate maximum norm. -/
theorem norm_basis_bracket_le {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C) (x y : L) :
    ‖b.equivFun ⁅x, y⁆‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) * ‖b.equivFun x‖ * ‖b.equivFun y‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro l
  change |b.repr ⁅x, y⁆ l| ≤ _
  rw [basis_bracket_coordinate b]
  calc
    _ ≤ ∑ i, ∑ j, |b.repr x i * b.repr y j * b.repr ⁅b i, b j⁆ l| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : J, ∑ _j : J, ‖b.equivFun x‖ * ‖b.equivFun y‖ * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      have hx : |b.repr x i| ≤ ‖b.equivFun x‖ := norm_le_pi_norm (b.equivFun x) i
      have hy : |b.repr y j| ≤ ‖b.equivFun y‖ := norm_le_pi_norm (b.equivFun y) j
      exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _))
        (hbracket i j l) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] <;> ring

theorem bracketWordLength_eq_nodes_add_one {I : Type} (w : FreeMagma I) :
    bracketWordLength w = bracketWordNodes w + 1 := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv => simp only [bracketWordLength, bracketWordNodes, hu, hv]; omega

/-- Evaluation of each Lie word is bounded by the number of its brackets and
letters. This is uniform over a family with bounded structure constants. -/
theorem norm_basis_evalBracketWord_le {I : Type} (X : I → L)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) (w : FreeMagma I) :
    ‖b.equivFun (evalBracketWord X w)‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) ^ bracketWordNodes w * M ^ bracketWordLength w := by
  let K : ℝ := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction w using FreeMagma.rec with
  | of i => simpa only [evalBracketWord, bracketWordNodes, bracketWordLength, pow_zero,
      pow_one, one_mul] using hX i
  | mul u v hu hv =>
    calc
      _ ≤ K * ‖b.equivFun (evalBracketWord X u)‖ * ‖b.equivFun (evalBracketWord X v)‖ :=
        norm_basis_bracket_le b hC hbracket _ _
      _ ≤ K * (K ^ bracketWordNodes u * M ^ bracketWordLength u) *
          (K ^ bracketWordNodes v * M ^ bracketWordLength v) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hu hK) hv
          (norm_nonneg _) (by positivity)
      _ = _ := by simp only [bracketWordNodes, bracketWordLength, pow_add, pow_one] <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded finite Dynkin expansions

The analytic BCH input is separated from its elementary coordinate estimate.
A degree-`c` expansion in right-nested words, with uniformly bounded
coefficients, has polynomial growth in the number of input factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

@[simp] theorem rightNestedWord_length {I : Type} (d : ℕ) (f : Fin (d + 1) → I) :
    bracketWordLength (rightNestedWord d f) = d + 1 := by
  rw [bracketWordLength_eq_nodes_add_one, rightNestedWord_nodes]

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- All coefficient counting and bracket estimates are proved here; only the
identity identifying this polynomial with the group product is external. -/
theorem norm_finiteDynkinPolynomial_le (b : Basis J ℝ L) {c n : ℕ}
    (coeff : DynkinCoefficients c n) (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (X : Fin n → L) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) :
    ‖b.equivFun (finiteDynkinPolynomial coeff X)‖ ≤
      (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + M) ^ c * (1 + (n : ℝ)) ^ c := by
  let K : ℝ := (Fintype.card J : ℝ) ^ 2 * C
  let A : ℝ := 2 ^ c * (1 + K) ^ c * (1 + M) ^ c
  have hK : 0 ≤ K := by positivity
  have hA : 0 ≤ A := by positivity
  have hterm (d : Fin c) (w : Fin (d.val + 1) → Fin n) :
      ‖b.equivFun (coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤ A := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    have hw := norm_basis_evalBracketWord_le b X hC hM hbracket hX
      (rightNestedWord d.val w)
    simp only [rightNestedWord_nodes, rightNestedWord_length] at hw
    have hkpow : K ^ d.val ≤ (1 + K) ^ c :=
      (pow_le_pow_left₀ hK (by linarith) d.val).trans
        (pow_le_pow_right₀ (by linarith) d.isLt.le)
    have hmpow : M ^ (d.val + 1) ≤ (1 + M) ^ c :=
      (pow_le_pow_left₀ hM (by linarith) (d.val + 1)).trans
        (pow_le_pow_right₀ (by linarith) d.isLt)
    have hw' : ‖b.equivFun (evalBracketWord X (rightNestedWord d.val w))‖ ≤
        (1 + K) ^ c * (1 + M) ^ c :=
      hw.trans (mul_le_mul hkpow hmpow (pow_nonneg hM _) (by positivity))
    have ht : |coeff d w| * ‖b.equivFun (evalBracketWord X (rightNestedWord d.val w))‖ ≤
        2 ^ c * ((1 + K) ^ c * (1 + M) ^ c) :=
      mul_le_mul (hcoeff d w) hw' (norm_nonneg _) (by positivity)
    simpa only [A, mul_assoc] using ht
  have hdegree (d : Fin c) :
      ‖b.equivFun (∑ w : Fin (d.val + 1) → Fin n,
        coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤
        A * (1 + (n : ℝ)) ^ c := by
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w : Fin (d.val + 1) → Fin n, A :=
        Finset.sum_le_sum (fun w _ => hterm d w)
      _ = (n : ℝ) ^ (d.val + 1) * A := by simp
      _ ≤ (1 + (n : ℝ)) ^ c * A := by
        apply mul_le_mul_of_nonneg_right _ hA
        exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) (d.val + 1)).trans
          (pow_le_pow_right₀ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) d.isLt)
      _ = _ := mul_comm _ _
  unfold finiteDynkinPolynomial
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : Fin c, A * (1 + (n : ℝ)) ^ c := Finset.sum_le_sum (fun d _ => hdegree d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [A, K] <;> ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateLieBrackets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Lie law in a chosen basis

Transport the original bracket to Euclidean coordinates, retaining its exact
word identities. A bound on basis structure constants gives a bound in the
finite-dimensional parameter space used for normalized-law compactness.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  (b : Basis (Fin n) ℝ L)

/-- The transported operation is a genuine Lie bracket, not only a bounded
bilinear operation. -/
theorem isLieBracket_basisBracket : IsLieBracket (basisBracket b) := by
  constructor
  · intro x
    simp
  · intro x y z
    simp only [basisBracket_apply, LinearEquiv.symm_apply_apply]
    rw [← map_add, ← leibniz_lie]


/-- The structure-constant estimate controls the norm of the actual law
in the fixed coordinate parameter space. -/
theorem norm_basisBracket_le {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ‖basisBracket b‖ ≤ (n : ℝ) ^ 2 * C := by
  apply norm_bilinear_le_of_bound (basisBracket b) (by positivity)
  intro x y
  have h := norm_basis_bracket_le b hC hb (b.equivFun.symm x) (b.equivFun.symm y)
  simpa only [basisBracket_apply, LinearEquiv.apply_symm_apply, Fintype.card_fin] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Exponential coordinates transfer the genuine group axioms, rather than
postulating them for a limiting polynomial. -/
theorem polynomialGroupLaws_of_exp {G : Type} [Group G]
    (m : V → V → V) (Exp : V → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hm : ∀ x y, Exp (m x y) = Exp x * Exp y) : PolynomialGroupLaws m := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hinj
    simp only [hm, mul_assoc]
  · intro x
    apply hinj
    rw [hm, hzero, one_mul]
  · intro x
    apply hinj
    rw [hm, hzero, mul_one]
  · intro x
    apply hinj
    rw [hm, hneg, inv_mul_cancel, hzero]
  · intro x s t
    apply hinj
    rw [hm, hadd]

/-- These group identities persist under convergence of the bracket data. -/
theorem isClosed_dynkinGroupLaws {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | PolynomialGroupLaws (dynkinProduct a B)} := by
  have hc (x y : V) : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B x y) :=
    continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
      continuous_id continuous_const continuous_const
  simp only [PolynomialGroupLaws, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id (hc x y) continuous_const)
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const (hc y z))
  refine (isClosed_iInter (fun x => isClosed_eq (hc 0 x) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc x 0) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc (-x) x) continuous_const)).inter ?_
  exact isClosed_iInter (fun x => isClosed_iInter (fun s =>
    isClosed_iInter (fun t => isClosed_eq (hc (s • x) (t • x)) continuous_const)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordBasisCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing actual word bases

Invertible selections from the coordinate matrix are exactly the actual word
bases. Thus the finite maximizing-basis argument applies to the Lie word list.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (X : I → L) (S : Finset (FreeMagma I))
  (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)

/-- Maximizing over actual bases also maximizes over every invertible column
selection. This connects the intrinsic list to the box coordinate estimates. -/
theorem exists_maximizing_wordBasis [Nonempty (WordBasisSelections X S)]
    (cost : S → ℝ) : ∃ β : WordBasisSelections X S,
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.exists_max_image Finset.univ
    (fun β : WordBasisSelections X S => columnBasisWeight cost β.val) Finset.univ_nonempty
  refine ⟨β, wordBasis_det_ne_zero X S b₀ β, ?_⟩
  intro w hw
  simpa only [wordBasisOfDet_val] using
    hβ (wordBasisOfDet X S b₀ w hw) (Finset.mem_univ _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive exponents of bracket words

Letter amplitudes add through every bracket. The sum in a word basis is the
letter-count expression used by the support datum.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I]

theorem sum_bracketWordExponent [Fintype J] (s : I → ℝ) (words : J → FreeMagma I) :
    ∑ j, bracketWordExponent s (words j) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * s i := by
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedWordBrackets
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalized structure constants

In a maximizing word basis, the bracket of two basis words is either zero
or another word of the finite list. Basis exchange then bounds every scaled
bracket coefficient independently of the letter amplitudes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- The algebraic structure-constant bound in the box-calculus lemma. -/
theorem exists_uniform_normalized_bracket_bound (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ (i j l : Fin (finrank ℝ L)) (r : ℝ), 0 ≤ r →
        |(WordBasisSelections.basis X (boundedBracketWords k) β).repr
            ⁅WordBasisSelections.basis X (boundedBracketWords k) β i,
              WordBasisSelections.basis X (boundedBracketWords k) β j⁆ l *
          Real.exp (r * (bracketWordExponent s (β.val i) +
            bracketWordExponent s (β.val j) - bracketWordExponent s (β.val l)))| ≤ C := by
  let S := boundedBracketWords (I := I) k
  let v := wordListCoordinates X S b₀
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_coordinate_bound v
  refine ⟨C, hC, ?_⟩
  intro s β hβ i j l r hr
  let b := WordBasisSelections.basis X S β
  by_cases hz : ⁅b i, b j⁆ = 0
  · change |b.repr ⁅b i, b j⁆ l * _| ≤ C
    rw [hz, map_zero, Finsupp.zero_apply, zero_mul, abs_zero]
    exact hC
  · let w : S := ⟨(β.val i : FreeMagma I) * β.val j, by
      apply (mem_boundedBracketWords _ _).mpr
      by_contra hn
      have hzero := evalBracketWord_eq_zero_of_depth X hk
        ((β.val i : FreeMagma I) * β.val j) (Nat.le_of_not_lt hn)
      have he : evalBracketWord X ((β.val i : FreeMagma I) * β.val j) = ⁅b i, b j⁆ := by
        rw [evalBracketWord_mul]
        exact congrArg₂ (fun x y : L => ⁅x, y⁆)
          (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
      exact hz (he.symm.trans hzero)⟩
    have he : evalBracketWord X w = ⁅b i, b j⁆ := by
      change ⁅evalBracketWord X (β.val i), evalBracketWord X (β.val j)⁆ = _
      exact congrArg₂ (fun x y : L => ⁅x, y⁆)
        (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
    have hc : columnCoordinates v β.val w l = b.repr ⁅b i, b j⁆ l := by
      rw [columnCoordinates_eq_wordBasis_repr X S b₀ β w]
      change b.repr (evalBracketWord X w) l = _
      rw [he]
    have hw : bracketWordExponent s w =
        bracketWordExponent s (β.val i) + bracketWordExponent s (β.val j) :=
      bracketWordExponent_mul s _ _
    have h := hbound (fun w => bracketWordExponent s w) β.val hβ w l r hr
    simpa only [hc, hw] using h

omit [FiniteDimensional ℝ L] in
theorem repr_exponentialRescaleBasis_bracket {J : Type}
    (b : Basis J ℝ L) (cost : J → ℝ) (r : ℝ) (i j l : J) :
    (exponentialRescaleBasis b cost r).repr
      ⁅exponentialRescaleBasis b cost r i, exponentialRescaleBasis b cost r j⁆ l =
      b.repr ⁅b i, b j⁆ l * Real.exp (r * (cost i + cost j - cost l)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val,
    smul_lie, lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← Real.exp_neg]
  have he : Real.exp (-(r * cost l)) * Real.exp (r * cost i) * Real.exp (r * cost j) =
      Real.exp (r * (cost i + cost j - cost l)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = b.repr ⁅b i, b j⁆ l *
        (Real.exp (-(r * cost l)) * Real.exp (r * cost i) * Real.exp (r * cost j)) := by ring
    _ = _ := by rw [he]

omit [FiniteDimensional ℝ L] in
/-- Uniform boundedness holds for the structure constants of the actual
rescaled Lie bracket, not just for a formal coefficient expression. -/
theorem exists_uniform_rescaled_structureConstant_bound (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ (r : ℝ), 0 ≤ r →
      let b := exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent s (β.val i)) r
      ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_bracket_bound X hk b₀
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr
  dsimp only
  intro i j l
  rw [repr_exponentialRescaleBasis_bracket]
  exact hbound s β hβ i j l r hr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanWordModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cartan word model

The support datum uses all ordered bases selected from a finite list that
contains every nonzero evaluated word. It is therefore attached to the Lie
algebra generators, rather than to an extra family of assumed bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace CartanWordModel

variable {H} (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℝ L] in
/-- No nonzero direction has been omitted by the finite cutoff. -/
theorem mem_wordList_of_eval_ne_zero (w : FreeMagma (Fin M.letterCount))
    (hw : evalBracketWord M.letter w ≠ 0) : w ∈ M.wordList := by
  apply (mem_boundedBracketWords _ _).mpr
  by_contra hn
  exact hw (evalBracketWord_eq_zero_of_depth M.letter M.bound_zero w (Nat.le_of_not_lt hn))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledGeneratorBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for normalized generator vectors

The same maximizing-basis exchange estimate which bounds structure constants
also bounds all exponentially rescaled generator vectors. Thus both parts of
the normalized Lie-law data lie in fixed bounded coordinate sets.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- Uniform boundedness of all rescaled letters in every maximizing word basis. -/
theorem exists_uniform_rescaled_generator_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (hS : ∀ i, FreeMagma.of i ∈ S) (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ i,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun
          (Real.exp (r * s i) • X i)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r).repr (Real.exp (r * s i) • X i) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have hh := hb (fun w => bracketWordExponent s w) β.val hβ ⟨.of i, hS i⟩ j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at hh
  simpa only [bracketWordExponent_of, evalBracketWord_of, Basis.equivFun_apply] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products in actual nilpotent exponential boxes

The published finite BCH identity is transported to a chosen Lie-algebra
model. The uniform normalized structure constants then give the polynomial
product bound in the manuscript's box calculus, for every height scale and
letter support. No coordinate growth conclusion is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The polynomial product estimate in any basis with bounded brackets. -/
theorem product_mem_exponentialCoordinateBox
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    {J : Type} [Fintype J] (b : Basis J ℝ L)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (g : Fin n → G) (hg : ∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) :
    (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
      ((c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + R) ^ c * (1 + (n : ℝ)) ^ c) := by
  choose X hX hbound using hg
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc n
  refine ⟨finiteDynkinPolynomial coeff X, ?_,
    norm_finiteDynkinPolynomial_le b coeff hcoeff X hC hR hbracket hbound⟩
  exact (hprod X).symm.trans (congrArg List.prod (congrArg List.ofFn (funext hX)))

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Uniform polynomial multiplication in all maximizing scaled word boxes.
The constant depends only on the fixed finite Lie model. -/
theorem exists_uniform_word_box_product_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords c)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → G,
      let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun i => bracketWordExponent s (β.val i)) r
      (∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) →
      (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
        (C * (1 + (n : ℝ)) ^ c * (1 + R) ^ c) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rescaled_structureConstant_bound X hc b₀
  refine ⟨(c : ℝ) * 2 ^ c * (1 + (finrank ℝ L : ℝ) ^ 2 * K) ^ c,
    by positivity, ?_⟩
  intro s β hβ r hr n R hR g
  dsimp only
  intro hg
  have hp := product_mem_exponentialCoordinateBox dynkin e Exp hExp hc
    (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
      (fun i => bracketWordExponent s (β.val i)) r)
    hK hR (hbound s β hβ r hr) g hg
  simpa only [Fintype.card_fin, mul_assoc, mul_left_comm, mul_comm] using hp

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact box exponents for the Cartan word model

The compact-template support equals the maximum of the determinant exponents
of the actual word boxes. This connects the Lie-algebra construction to the
Euclidean coordinate-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory
open scoped BigOperators

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The determinant exponent of each basis is its template support sum. -/
theorem columnBasisWeight_boxCost (E : Set W) (β : M.Bases) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).basisTemplateSupport E β := by
  unfold columnBasisWeight boxCost
  rw [sum_bracketWordExponent]
  rfl

set_option maxHeartbeats 1000000 in
/-- Maximizing the finite word-box determinant gives exactly `P(E)`. -/
theorem exists_maximizing_box_basis
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) : ∃ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod e E) β.val ∧
      columnBasisWeight (M.boxCost T hunimod e E) β.val =
        (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod e E)
  refine ⟨β, hβ, le_antisymm ?_ ?_⟩
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · apply (M.supportIn T hunimod e).templateSupport_le
    intro γ
    rw [← M.columnBasisWeight_boxCost T hunimod e E γ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGroupBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group boxes for the Cartan word model

The finite Cartan construction supplies the bases, bracket bounds, nilpotence
and support exponents used here. The only external group facts are the two
explicit published exponential inputs. In particular no box multiplication or
volume estimate is an assumption.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)

include hExp

set_option maxHeartbeats 1000000 in
/-- A uniform product estimate for the actual Cartan boxes. No assumptions
about compactness or convexity of the template are needed for this part. -/
theorem exists_groupBox_product_bound
    (dynkin : NilpotentDynkinExpansionInput EN N)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → N,
      (∀ i, g i ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r R) →
      (List.ofFn g).prod ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β r
        (C * (1 + (n : ℝ)) ^ M.bound * (1 + R) ^ M.bound) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_word_box_product_bound dynkin eN Exp hExp
    M.letter M.bound_zero b₀
  exact ⟨C, hC, fun E β hβ r hr n R hR g hg =>
    hbound ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr n R hR g hg⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating root-action bounds through Cartan boxes

A Lie map which preserves the letter root spaces has a polynomial bound in
every maximizing box. The proof propagates the bounds on letters through
actual bracket words, then through their coordinate basis. This is the
algebraic step in the box-conjugation estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators Manifold

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
/-- Independent exponential scaling of letters multiplies a word by the
exponential of the sum of its letter exponents. -/
theorem evalBracketWord_exp_smul (X : I → L) (s : I → ℝ) (r : ℝ) (w : FreeMagma I) :
    evalBracketWord (fun i => Real.exp (r * s i) • X i) w =
      Real.exp (r * bracketWordExponent s w) • evalBracketWord X w := by
  induction w using FreeMagma.rec with
  | of i => simp only [evalBracketWord_of, bracketWordExponent_of]
  | mul u v hu hv =>
    change evalBracketWord (fun i => Real.exp (r * s i) • X i) (u * v) =
      Real.exp (r * bracketWordExponent s (u * v)) • evalBracketWord X (u * v)
    rw [evalBracketWord_mul, hu, hv, smul_lie, lie_smul, smul_smul,
      ← Real.exp_add, bracketWordExponent_mul, mul_add, evalBracketWord_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RescaledLieFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual rescalings lie in a compact family of normalized Lie laws

Both the law and the generator vectors are transported by the same rescaled
word basis. Basis-word identities hold exactly, independently of the scale.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I]

/-- A selected rescaled word is exactly its coordinate unit vector. -/
theorem rescaledLieData_word (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (s : I → ℝ) (r : ℝ)
    (j : Fin (finrank ℝ L)) :
    evalBilinearWord (rescaledLieData X S β s r).1
      (rescaledLieData X S β s r).2 (β.val j) = Pi.single j 1 := by
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  change evalBilinearWord (basisBracket b)
    (fun i => b.equivFun (Real.exp (r * s i) • X i)) (β.val j) = _
  rw [evalBilinearWord_basisBracket, evalBracketWord_exp_smul]
  have he : Real.exp (r * bracketWordExponent s (β.val j)) •
      evalBracketWord X (β.val j) = b j := by
    have hw := WordBasisSelections.eval_words X S β j
    change evalBracketWord X (β.val j) = _ at hw
    rw [hw]
    simp only [b, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0]
  rw [he]
  ext k
  simp [Pi.single_apply, eq_comm]

/-- A single bound works for all maximizing rescalings. For any fixed word
basis, their closure is contained in the compact normalized parameter set. -/
theorem exists_rescaledLieData_bound (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r →
      rescaledLieData X (boundedBracketWords k) β s r ∈
        normalizedLieParameters (fun j => (β.val j : FreeMagma I))
          (fun j => Pi.single j 1) C := by
  obtain ⟨A, hA, ha⟩ := exists_uniform_rescaled_structureConstant_bound X hk b₀
  obtain ⟨D, hD, hd⟩ := exists_uniform_rescaled_generator_bound X
    (boundedBracketWords k) hletters b₀
  let C := max ((finrank ℝ L : ℝ) ^ 2 * A) D
  refine ⟨C, le_trans hD (le_max_right _ _), ?_⟩
  intro s β hβ r hr
  let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
    (fun j => bracketWordExponent s (β.val j)) r
  refine ⟨?_, ?_, isLieBracket_basisBracket b, rescaledLieData_word X _ β s r⟩
  · exact (norm_basisBracket_le b hA (ha s β hβ r hr)).trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg (le_trans hD (le_max_right _ _))).mpr
    intro i
    exact (hd s β hβ r hr i).trans (le_max_right _ _)

namespace CartanWordModel

variable [FiniteDimensional ℝ L] {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]

omit [FiniteDimensional ℝ L] in
/-- Every actual Cartan letter occurs in the finite word list. -/
theorem letter_mem_wordList (M : CartanWordModel H) (i : Fin M.letterCount) :
    FreeMagma.of i ∈ M.wordList := by
  apply M.mem_wordList_of_eval_ne_zero
  change M.letter i ≠ 0
  intro hi
  have h := M.letter_quotient i
  rw [hi, map_zero] at h
  exact M.abelianBasis.ne_zero i h.symm

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_mul _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_neg _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp_zero _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact polynomial group laws for the actual rescalings

One fixed binary Dynkin formula suffices for all coordinate bases of the
original group. Its group and one-parameter identities are proved in each
basis, and closedness preserves them in the compact normalized family.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

variable {V I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

/-- The actual polynomial group laws define a closed part of the compact
normalized Lie parameter space. -/
theorem isCompact_normalizedGroupParameters {c : ℕ} (a : DynkinCoefficients c 2)
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedGroupParameters a w b C) :=
  (isCompact_normalizedLieParameters w b C).inter_right
    ((isClosed_dynkinGroupLaws a).preimage continuous_fst)

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  {G : Type} [Group G]

/-- The binary polynomial in any basis is the genuine product in exponential
coordinates. No fresh Dynkin coefficients are chosen on rescaling. -/
theorem basis_polynomialGroupLaws (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    PolynomialGroupLaws (dynkinProduct a (basisBracket b)) := by
  apply polynomialGroupLaws_of_exp _ (Exp ∘ b.equivFun.symm)
    (hinj.comp b.equivFun.symm.injective)
  · simpa using hzero
  · intro x
    simpa using hneg (b.equivFun.symm x)
  · intro x s t
    simpa using hadd (b.equivFun.symm x) s t
  · intro x y
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    simp only [Function.comp_apply, he, LinearEquiv.symm_apply_apply]
    exact hm _ _

variable [DecidableEq I]

/-- Every maximizing rescaling lies in a compact parameter space in which
both generation and the group identities persist. -/
theorem exists_rescaledGroupData_bound (X : I → L) {k : ℕ}
    (hk : LieModule.lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r →
      rescaledLieData X (boundedBracketWords k) β s r ∈
        normalizedGroupParameters a (fun j => (β.val j : FreeMagma I))
          (fun j => Pi.single j 1) C := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledLieData_bound X hk hletters b₀
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr
  refine ⟨hb s β hβ r hr, ?_⟩
  exact basis_polynomialGroupLaws _ Exp hinj hzero hneg hadd a hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation identities persist under coordinate limits

The exponential of the coordinate adjoint is the genuine logarithmic
conjugation map. This identity is closed in the bracket parameter and will
identify the columns of the limiting generator endpoint map.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The logarithmic conjugation identity is a closed condition. -/
theorem isClosed_exponentialConjugationLaw {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V |
      ExponentialConjugationLaw (dynkinProduct a B) B} := by
  let : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _
  simp only [ExponentialConjugationLaw, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro t
  have hc : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B (t • x) y) :=
    continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const continuous_const
  apply isClosed_eq
  · exact continuous_dynkinProduct (V := V) a id _ _
      continuous_id hc continuous_const
  · exact (NormedSpace.exp_continuous.comp
      ((ContinuousLinearMap.apply ℝ (V →L[ℝ] V) x).continuous.const_smul t)).clm_apply
        continuous_const

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.coordinateConjugationNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.coordinateConjugationNormedSpace
/-- Coordinate change intertwines actual adjoint exponentials. -/
theorem basis_exp_adjoint {n : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (x y : L) (t : ℝ) :
    b.equivFun (NormedSpace.exp (t • continuousAd x) y) =
      NormedSpace.exp (t • basisBracket b (b.equivFun x)) (b.equivFun y) := by
  let f : L →L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  apply exp_intertwine_apply f
  intro z
  change b.equivFun (t • ⁅x, z⁆) =
    t • b.equivFun ⁅b.equivFun.symm (b.equivFun x), b.equivFun.symm (b.equivFun z)⁆
  simp only [map_smul, LinearEquiv.symm_apply_apply]

variable {G A : Type} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation-derived conjugation formula transports to every
coordinate basis with the same binary Dynkin coefficients. -/
theorem basis_exponentialConjugationLaw {n c : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ExponentialConjugationLaw (dynkinProduct a (basisBracket b)) (basisBracket b) := by
  have hp (x y : Fin n → ℝ) :
      Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
        Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm]
  intro x y t
  apply hinj.comp b.equivFun.symm.injective
  change Exp (b.equivFun.symm _) = Exp (b.equivFun.symm _)
  rw [hp, hp, map_neg, hneg, map_smul]
  have hc := basis_exp_adjoint b (b.equivFun.symm x) (b.equivFun.symm y) t
  simp only [LinearEquiv.apply_symm_apply] at hc
  have he := congrArg b.equivFun.symm hc
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [← he]
  exact (exp_ad_eq_group_conjugation Exp j ρ hρ hmatch _ _ t).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generator schemes with locally open endpoint maps

A conjugated-generator basis gives a single finite scheme, with fixed
conjugating words, whose endpoint map covers a neighborhood of the identity.
The logarithm of that map has the identity-rank differential proved from BCH.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type} [Group G]

variable (X : I → L) (Exp : L → G)

attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedSpace
theorem generatorGroupWord_append (u v : List (I × ℝ)) :
    generatorGroupWord X Exp (u ++ v) =
      generatorGroupWord X Exp u * generatorGroupWord X Exp v := by
  simp only [generatorGroupWord, List.map_append, List.prod_append]

theorem generatorGroupWord_inverse (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, generatorGroupWord_append, generatorGroupWord_cons,
      generatorGroupWord_nil, mul_one, mul_inv_rev] at *
    rw [ih]
    congr 1
    simpa only [neg_smul] using hneg (t • X i)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The group carried by a polynomial coordinate law

This type keeps the group multiplication distinct from vector addition. The
exponential-coordinate bijection is the identity on underlying points.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The direct polynomial evaluation is exactly the generator group word. -/
theorem exp_polynomialWord (m : V → V → V) (h : PolynomialGroupLaws m)
    (X : I → V) (w : List (I × ℝ)) :
    PolynomialCoordinateGroup.exp m h (polynomialWord m X w) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp m h) w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    change PolynomialCoordinateGroup.exp m h
      (m (t • X i) (polynomialWord m X w)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih, generatorGroupWord_cons]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PolynomialEndpointSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

theorem exp_polynomialListProduct (m : V → V → V) (h : PolynomialGroupLaws m)
    (xs : List V) :
    PolynomialCoordinateGroup.exp m h (polynomialListProduct m xs) =
      (xs.map (PolynomialCoordinateGroup.exp m h)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change PolynomialCoordinateGroup.exp m h (m x (polynomialListProduct m xs)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih]
    rfl

theorem contDiff_polynomialWord {c : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → I → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) (w : List (I × ℝ)) :
    ContDiff ℝ k (fun p => polynomialWord (dynkinProduct a (B p)) (X p) w) := by
  induction w with
  | nil => exact contDiff_const
  | cons z w ih =>
    rcases z with ⟨i, t⟩
    exact contDiff_dynkinProduct a B _ _ hB ((hX i).const_smul t) ih

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

variable [Fintype I]

/-- Joint smoothness includes the law and generator data, rather than just
the inserted amplitudes at one fixed law. -/
theorem contDiff_polynomialEndpointScheme {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (w : Fin n → List (I × ℝ)) (i : Fin n → I) :
    ContDiff ℝ k (fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin n → ℝ) =>
      polynomialEndpointScheme a w i z.1 z.2) := by
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    apply contDiff_dynkinProduct
    · exact contDiff_fst.fst
    · apply contDiff_dynkinProduct
      · exact contDiff_fst.fst
      · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
          (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (w j)
      · exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).smul
          ((contDiff_apply ℝ V (i j)).comp contDiff_fst.snd)
    · exact contDiff_polynomialWord a _ _ contDiff_fst.fst
        (fun l => (contDiff_apply ℝ V l).comp contDiff_fst.snd) (inverseGeneratorWord (w j))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AmplitudeWordCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently varying every amplitude in a fixed generator word -/

noncomputable section

namespace PolycyclicRecognition

theorem contDiff_amplitudeWordEndpoint {I : Type} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I) {q : ℕ∞} :
    ContDiff ℝ q (fun z :
      (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
        (Fin m → ℝ) => amplitudeWordEndpoint (n := n) a letters z.1 z.2) := by
  apply contDiff_polynomialListProduct_ofFn
  · exact contDiff_fst.fst
  · intro j
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).smul
      ((contDiff_apply ℝ (Fin n → ℝ) (letters j)).comp contDiff_fst.snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateSchemeBasis
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nondegenerate schemes in limiting coordinate groups

The preserved adjoint-conjugation identity turns the spanning adjoint orbits
into actual group-word conjugates. Their polynomial endpoint map is exactly
the ordered exponential product in the resulting basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The coordinate adjoint word is realized by the corresponding generator
word in the polynomial coordinate group. -/
theorem exp_bilinearAdjointWord (m : V → V → V) (hg : PolynomialGroupLaws m)
    (B : V →L[ℝ] V →L[ℝ] V) (hc : ExponentialConjugationLaw m B)
    (X : I → V) (w : List (I × ℝ)) (v : V) :
    PolynomialCoordinateGroup.exp m hg (bilinearAdjointWord B X w v) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp m hg) w *
        PolynomialCoordinateGroup.exp m hg v *
        (generatorGroupWord X (PolynomialCoordinateGroup.exp m hg) w)⁻¹ := by
  have he (x y : V) (t : ℝ) :
      PolynomialCoordinateGroup.exp m hg (NormedSpace.exp (t • B x) y) =
        PolynomialCoordinateGroup.exp m hg (t • x) *
          PolynomialCoordinateGroup.exp m hg y *
          (PolynomialCoordinateGroup.exp m hg (t • x))⁻¹ := by
    rw [← hc x y t]
    rfl
  induction w with
  | nil => simp [bilinearAdjointWord]
  | cons z w ih =>
    rcases z with ⟨i, t⟩
    change PolynomialCoordinateGroup.exp m hg
      (NormedSpace.exp (t • B (X i)) (bilinearAdjointWord B X w v)) = _
    rw [he, ih, generatorGroupWord_cons]
    group

/-- Expanding a polynomial scheme gives its actual generator word. -/
theorem exp_polynomialEndpointScheme {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B)) (X : I → V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I) (t : Fin n → ℝ) :
    PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      (polynomialEndpointScheme a w i (B, X) t) =
    generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
      (generatorSchemeWord w i t) := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  unfold polynomialEndpointScheme
  rw [exp_polynomialListProduct, List.map_ofFn]
  unfold generatorSchemeWord generatorGroupWord
  rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  change PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
    (dynkinProduct a B
      (dynkinProduct a B (polynomialWord (dynkinProduct a B) X (w k)) (t k • X (i k)))
      (polynomialWord (dynkinProduct a B) X (inverseGeneratorWord (w k)))) =
    generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
      (w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k))
  rw [PolynomialCoordinateGroup.exp_mul, PolynomialCoordinateGroup.exp_mul,
    exp_polynomialWord, exp_polynomialWord,
    generatorGroupWord_append, generatorGroupWord_append]
  simp only [generatorGroupWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- The polynomial formula of a chosen conjugate scheme is the genuine
ordered basis product whenever the parameters satisfy the group laws. -/
theorem polynomialEndpointScheme_basisProduct {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B))
    (X : I → V) (b : Basis (Fin n) ℝ V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hb : ∀ k (s : ℝ), PolynomialCoordinateGroup.exp (dynkinProduct a B) hg (s • b k) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) (w k) *
        PolynomialCoordinateGroup.exp (dynkinProduct a B) hg (s • X (i k)) *
        (generatorGroupWord X (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) (w k))⁻¹)
    (t : Fin n → ℝ) :
    PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
      (polynomialEndpointScheme a w i (B, X) t) =
        basisExponentialProduct (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) b t := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  unfold polynomialEndpointScheme
  rw [exp_polynomialListProduct, List.map_ofFn]
  unfold basisExponentialProduct
  congr 1
  apply congrArg List.ofFn
  funext k
  change PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
    (dynkinProduct a B
      (dynkinProduct a B (polynomialWord (dynkinProduct a B) X (w k)) (t k • X (i k)))
      (polynomialWord (dynkinProduct a B) X (inverseGeneratorWord (w k)))) = _
  rw [PolynomialCoordinateGroup.exp_mul, PolynomialCoordinateGroup.exp_mul,
    exp_polynomialWord, exp_polynomialWord,
    generatorGroupWord_inverse X _ (PolynomialCoordinateGroup.exp_neg _ _) (w k)]
  exact (hb k (t k)).symm

/-- Every normalized word-generated limiting law has an actual basis
scheme. Its smoothness is proved independently in `PolynomialEndpointSchemes`. -/
theorem exists_coordinate_basis_scheme {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V)
      (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I),
      ∀ t, PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
        (polynomialEndpointScheme a w i (B, X) t) =
          basisExponentialProduct (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg) b t := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  obtain ⟨b, w, i, hb⟩ := exists_bilinearOrbit_basis B hB X b₀ w₀ hw₀
  refine ⟨b, w, i, ?_⟩
  apply polynomialEndpointScheme_basisProduct a B hB hg X b w i
  intro k s
  rw [← hb k, ← map_smul]
  exact exp_bilinearAdjointWord _ hg B hc X (w k) (s • X (i k))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedExponentialLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact normalized exponential-coordinate groups

The defining equations retain both the exact group law and its adjoint
conjugation formula. All of these equations hold in the actual rescalings
and survive passage to a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Module

variable {V I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

theorem isCompact_normalizedExponentialParameters {c : ℕ}
    (a : DynkinCoefficients c 2) (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedExponentialParameters a w b C) :=
  (isCompact_normalizedGroupParameters a w b C).inter_right
    ((isClosed_exponentialConjugationLaw a).preimage continuous_fst)

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [DecidableEq I] {G A : Type} [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Actual rescalings satisfy all the closed equations used in the limiting
endpoint-map argument. No limiting-group assertion is an external input. -/
theorem exists_rescaledExponentialData_bound (X : I → L) {k : ℕ}
    (hk : LieModule.lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r →
      rescaledLieData X (boundedBracketWords k) β s r ∈
        normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I))
          (fun j => Pi.single j 1) C := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledGroupData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr
  refine ⟨hb s β hβ r hr, ?_⟩
  exact basis_exponentialConjugationLaw _ Exp hinj hneg a hm j ρ hρ hmatch

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateSchemeSubmersion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local images for the actual normalized coordinate family

The endpoint differential is computed from exact coordinate-axis curves.
Its columns form a basis at every limiting law, so the compact submersion
theorem supplies a common image ball and finitely many schemes.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The differential in the amplitude directions is determined by the
coordinate-axis identities, without differentiating any group operations. -/
theorem partial_fderiv_eq_basis {n : ℕ}
    (f : P × (Fin n → ℝ) → V) (p : P) (b : Basis (Fin n) ℝ V)
    (hd : DifferentiableAt ℝ f (p, 0))
    (haxis : ∀ i s, f (p, Pi.single i s) = s • b i) (t : Fin n → ℝ) :
    fderiv ℝ f (p, 0) (0, t) = b.equivFun.symm t := by
  have hcol (i : Fin n) : fderiv ℝ f (p, 0) (0, Pi.single i 1) = b i := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) p).prodMk (hasDerivAt_single i (0 : ℝ))) (by simp)
    have he : (fun s : ℝ => f (p, Pi.single i s)) = fun s => s • b i := by
      funext s
      exact haxis i s
    change HasDerivAt (fun s : ℝ => f (p, Pi.single i s)) _ 0 at h
    rw [he] at h
    exact h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (b i))
  have ht : ((0 : P), t) = ∑ i : Fin n, t i • ((0 : P), Pi.single i (1 : ℝ)) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero]
    · simpa only [Prod.snd_sum, Prod.smul_snd] using (pi_eq_sum_univ' t)
  rw [ht, map_sum]
  simp only [map_smul, hcol]
  simpa only [LinearEquiv.apply_symm_apply] using b.sum_equivFun (b.equivFun.symm t)

variable {I : Type} [Fintype I] [FiniteDimensional ℝ V]

/-- Every limiting normalized law admits a polynomial generator scheme with
surjective amplitude differential at the identity. -/
theorem exists_coordinate_submersive_scheme {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (w : Fin (finrank ℝ V) → List (I × ℝ)) (i : Fin (finrank ℝ V) → I),
      polynomialEndpointScheme a w i (B, X) 0 = 0 ∧
      Function.Surjective (fun t : Fin (finrank ℝ V) → ℝ =>
        fderiv ℝ (fun z => polynomialEndpointScheme a w i z.1 z.2) ((B, X), 0) (0, t)) := by
  obtain ⟨b, w, i, he⟩ := exists_coordinate_basis_scheme a B hB hg hc X b₀ w₀ hw₀
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  have hzero : polynomialEndpointScheme a w i (B, X) 0 = 0 := by
    apply Exp.injective
    rw [he]
    simp [Exp, basisExponentialProduct]
  have haxis (j : Fin (finrank ℝ V)) (s : ℝ) :
      polynomialEndpointScheme a w i (B, X) (Pi.single j s) = s • b j := by
    apply Exp.injective
    rw [he]
    unfold basisExponentialProduct
    rw [list_prod_ofFn_eq_single _ j (by
      intro k hk
      simp [Pi.single_eq_of_ne hk])]
    simp [Exp]
  refine ⟨w, i, hzero, ?_⟩
  have hd := (contDiff_polynomialEndpointScheme (V := V) (k := 1) a w i).differentiable one_ne_zero
  intro y
  refine ⟨b.equivFun y, ?_⟩
  change fderiv ℝ (fun z => polynomialEndpointScheme a w i z.1 z.2)
    ((B, X), 0) (0, b.equivFun y) = y
  rw [partial_fderiv_eq_basis _ (B, X) b (hd _) haxis, LinearEquiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ExpandedSchemeAmplitudes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conjugate scheme inside a word with independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

variable {I : Type} {n d c : ℕ}

theorem map_schemeAmplitudeSlots (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (schemeAmplitudeSlots w i).map (fun p => (p.1, evaluateAmplitudeSlot t p.2)) =
      generatorSchemeWord w i t := by
  simp [schemeAmplitudeSlots, generatorSchemeWord, List.map_flatten,
    List.map_map, List.map_ofFn, evaluateAmplitudeSlot, Function.comp_def]

/-- All amplitudes of the expanded word are smooth affine functions of the
original inserted coordinates. -/
theorem contDiff_evaluateAmplitudeSlots (l : List (I × (ℝ ⊕ Fin n))) {q : ℕ∞} :
    ContDiff ℝ q (fun t : Fin n → ℝ => fun j : Fin l.length =>
      evaluateAmplitudeSlot t (l.get j).2) := by
  apply contDiff_pi.mpr
  intro j
  cases (l.get j).2 with
  | inl r => exact contDiff_const
  | inr k => exact contDiff_apply ℝ ℝ k

theorem polynomialWord_eq_listProduct {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (m : V → V → V) (X : I → V) (l : List (I × ℝ)) :
    polynomialWord m X l =
      polynomialListProduct m (l.map (fun p => p.2 • X p.1)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨i, t⟩
    simpa only [polynomialWord, List.map_cons, polynomialListProduct] using congrArg (m (t • X i)) ih

/-- Flattening the slots preserves the genuine endpoint at every group law. -/
theorem amplitudeWord_scheme_eq (a : DynkinCoefficients c 2)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (X : I → Fin d → ℝ) (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    amplitudeWordEndpoint a (fun j => ((schemeAmplitudeSlots w i).get j).1) (B, X)
      (fun j => evaluateAmplitudeSlot t ((schemeAmplitudeSlots w i).get j).2) =
        polynomialEndpointScheme a w i (B, X) t := by
  let l := schemeAmplitudeSlots w i
  have he : (List.ofFn fun j : Fin l.length =>
      ((l.get j).1, evaluateAmplitudeSlot t (l.get j).2)) = generatorSchemeWord w i t := by
    change List.ofFn ((fun p => (p.1, evaluateAmplitudeSlot t p.2)) ∘ l.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
    exact map_schemeAmplitudeSlots w i t
  have hw : amplitudeWordEndpoint a (fun j => (l.get j).1) (B, X)
      (fun j => evaluateAmplitudeSlot t (l.get j).2) =
      polynomialWord (dynkinProduct a B) X (generatorSchemeWord w i t) := by
    rw [polynomialWord_eq_listProduct, ← he]
    simp only [List.map_ofFn, amplitudeWordEndpoint, Function.comp_def]
  rw [hw]
  apply (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg).injective
  rw [exp_polynomialWord, exp_polynomialEndpointScheme a B hB hg]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AmplitudeWordRank
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full rank of one fixed independent generator word -/

noncomputable section

namespace PolycyclicRecognition

open Module

/-- The rank belongs to the full word, before any successful-parameter restriction. -/
theorem exists_submersive_amplitudeWord {I J : Type} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → Fin n → ℝ) (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (m : ℕ) (letters : Fin m → I) (t₀ : Fin m → ℝ),
      amplitudeWordEndpoint a letters (B, X) t₀ = 0 ∧
      Function.Surjective (fderiv ℝ (amplitudeWordEndpoint a letters (B, X)) t₀) := by
  obtain ⟨w, i, hz, hs⟩ := exists_coordinate_submersive_scheme a B hB hg hc X b₀ w₀ hw₀
  let l := schemeAmplitudeSlots w i
  let letters := fun j : Fin l.length => (l.get j).1
  let ψ := fun t : Fin (finrank ℝ (Fin n → ℝ)) → ℝ =>
    fun j : Fin l.length => evaluateAmplitudeSlot t (l.get j).2
  let f := amplitudeWordEndpoint a letters (B, X)
  have he : (fun t => f (ψ t)) = polynomialEndpointScheme a w i (B, X) := by
    funext t
    exact amplitudeWord_scheme_eq a B hB hg X w i t
  have hψ : DifferentiableAt ℝ ψ 0 :=
    ((contDiff_evaluateAmplitudeSlots (q := 1) l).differentiable one_ne_zero).differentiableAt
  have hf : DifferentiableAt ℝ f (ψ 0) := by
    exact (((contDiff_amplitudeWordEndpoint (q := 1) a letters).comp
      (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero).differentiableAt
  have hd0 := (contDiff_polynomialEndpointScheme (V := Fin n → ℝ) (k := 1) a w i).differentiable one_ne_zero
  have hd1 := (hd0 ((B, X), 0)).hasFDerivAt
  have hi := hasFDerivAt_prodMk_right (𝕜 := ℝ) (B, X) (0 : Fin (finrank ℝ (Fin n → ℝ)) → ℝ)
  have hd := hd1.comp (0 : Fin (finrank ℝ (Fin n → ℝ)) → ℝ) hi
  have hd' := hf.hasFDerivAt.comp 0 hψ.hasFDerivAt
  change HasFDerivAt (fun t => f (ψ t)) _ 0 at hd'
  rw [he] at hd'
  have hderiv := hd'.unique hd
  refine ⟨l.length, letters, ψ 0, ?_, ?_⟩
  · change f (ψ 0) = 0
    rw [congrFun he 0]
    exact hz
  · intro y
    obtain ⟨v, hv⟩ := hs y
    refine ⟨fderiv ℝ ψ 0 v, ?_⟩
    have hh := congrArg (fun A => A v) hderiv
    exact hh.trans hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateBilinearExpansion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-coordinate expansion of the transported Lie bracket -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Every coordinate bracket is the finite linear combination of its
structure constants and elementary bilinear maps. -/
theorem basisBracket_eq_coordinate_sum
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) :
    basisBracket b = ∑ i, ∑ j, ∑ k,
      b.repr ⁅b i, b j⁆ k • coordinateBilinearUnit i j k := by
  ext x y k
  rw [basisBracket_apply]
  change b.repr ⁅b.equivFun.symm x, b.equivFun.symm y⁆ k = _
  rw [basis_bracket_coordinate]
  simp only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp [Pi.smul_apply, Pi.single_apply, mul_comm, mul_assoc]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentConjugationDecay
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential slack survives polynomial nilpotent conjugation

Choosing the chart margin larger than the nilpotence degree times the
expanded-box exponent allows an operator-norm argument for interior slack.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A uniformly nilpotent operator can grow exponentially more slowly than
its input contracts. Its exponential still sends that input to zero. -/
theorem nilpotent_exp_apply_tendsto_zero_of_exponent_gap
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp (α * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp (-β * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let C := ((m : ℝ) + 1) * (1 + A) ^ m * 2 ^ m * B
  have hC : 0 ≤ C := by positivity
  have hbound (r : ℝ) (hr : 0 ≤ r)
      (hNr : ‖N r‖ ≤ A * Real.exp (α * r))
      (hvr : ‖v r‖ ≤ B * Real.exp (-β * r)) :
      ‖NormedSpace.exp (N r) (v r)‖ ≤ C * Real.exp (((m : ℝ) * α - β) * r) := by
    have hexp : 1 ≤ Real.exp (α * r) := Real.one_le_exp (mul_nonneg hα hr)
    have hbase : 1 + ‖N r‖ ≤ (1 + A) * Real.exp (α * r) := by
      nlinarith [hNr]
    have he := norm_exp_smul_nilpotent_le (N r) (hnil r) (t := 1) zero_le_one
    simp only [one_smul, one_add_one_eq_two] at he
    calc
      _ ≤ ‖NormedSpace.exp (N r)‖ * ‖v r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (((m : ℝ) + 1) * (1 + ‖N r‖) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := mul_le_mul he hvr (norm_nonneg _) (by positivity)
      _ ≤ (((m : ℝ) + 1) * ((1 + A) * Real.exp (α * r)) ^ m * 2 ^ m) *
          (B * Real.exp (-β * r)) := by gcongr
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        calc
          _ = C * (Real.exp ((m : ℝ) * (α * r)) * Real.exp (-β * r)) := by dsimp [C] <;> ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (((m : ℝ) * α - β) * r)) atTop (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => ((m : ℝ) * α - β) * r) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.mpr hgap)).mpr tendsto_id
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ), hN, hv] with r hr hNr hvr
  exact hbound r hr hNr hvr

/-- The same exponential gap absorbs a common subexponential envelope in
both the conjugating operator and the translated vector. -/
theorem nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : ℝ → V →L[ℝ] V) (v : ℝ → V) {m : ℕ}
    (hnil : ∀ r, (N r) ^ (m + 1) = 0)
    {A B α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hgap : (m : ℝ) * α < β)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ A * Real.exp ((α + ε r) * r))
    (hv : ∀ᶠ r : ℝ in atTop, ‖v r‖ ≤ B * Real.exp ((-β + ε r) * r)) :
    Tendsto (fun r => NormedSpace.exp (N r) (v r)) atTop (𝓝 0) := by
  let δ := (β - (m : ℝ) * α) / (2 * ((m : ℝ) + 1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hδε : ∀ᶠ r : ℝ in atTop, ε r < δ := hε.eventually (eventually_lt_nhds hδ)
  have hδeq : δ * (2 * ((m : ℝ) + 1)) = β - (m : ℝ) * α := by
    dsimp [δ]
    field_simp
  have hgap' : (m : ℝ) * (α + δ) < β - δ := by nlinarith
  apply nilpotent_exp_apply_tendsto_zero_of_exponent_gap N v hnil hA hB
    (by positivity : 0 ≤ α + δ) hgap'
  · filter_upwards [hN, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hA)
  · filter_upwards [hv, hδε, eventually_ge_atTop (0 : ℝ)] with r hr he hr0
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hB)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BasisAdjointNilpotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform nilpotence exponent for every coordinate adjoint -/

namespace PolycyclicRecognition

open Module LieModule

/-- Coordinate adjoints are uniformly nilpotent at any index at which the
actual lower central series vanishes. -/
theorem basisBracket_pow_eq_zero
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n k : ℕ}
    (b : Basis (Fin n) ℝ L) (hk : lowerCentralSeries ℝ L L k = ⊥)
    (x : Fin n → ℝ) : (basisBracket b x) ^ k = 0 := by
  have hiter (j : ℕ) (y : Fin n → ℝ) :
      ((basisBracket b x) ^ j) y =
        b.equivFun ((toEnd ℝ L L (b.equivFun.symm x))^[j] (b.equivFun.symm y)) := by
    induction j generalizing y with
    | zero =>
      change y = b.equivFun (b.equivFun.symm y)
      exact (b.equivFun.apply_symm_apply y).symm
    | succ j ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      simp only [basisBracket_apply, LinearEquiv.symm_apply_apply,
        Function.iterate_succ_apply]
      rfl
  apply ContinuousLinearMap.ext
  intro y
  rw [hiter]
  have hz := iterate_toEnd_mem_lowerCentralSeries ℝ L L
    (b.equivFun.symm x) (b.equivFun.symm y) k
  rw [hk] at hz
  have heq : (toEnd ℝ L L (b.equivFun.symm x))^[k] (b.equivFun.symm y) = 0 :=
    hz
  rw [heq, map_zero]
  rfl

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateConjugationDecay
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interior slack for conjugation in varying actual coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

/-- A sufficiently large exponential margin survives conjugation by every
expanded-box coordinate, uniformly over a bounded family of actual brackets.
The exact exponential-conjugation law is provided by the existing faithful
realization theorem in the application. -/
theorem coordinate_conjugation_tendsto_zero
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n m c : ℕ}
    [Nonempty (Fin n)]
    (b : ℝ → Basis (Fin n) ℝ L)
    (hk : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (a : DynkinCoefficients c 2)
    (hconj : ∀ r, ExponentialConjugationLaw
      (dynkinProduct a (basisBracket (b r))) (basisBracket (b r)))
    (k y : ℝ → Fin n → ℝ)
    {C A B α β : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hbound : ∀ᶠ r : ℝ in atTop, ‖basisBracket (b r)‖ ≤ C)
    (hgap : (m : ℝ) * α < β)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hksize : ∀ᶠ r : ℝ in atTop, ‖k r‖ ≤ A * Real.exp ((α + ε r) * r))
    (hysize : ∀ᶠ r : ℝ in atTop, ‖y r‖ ≤ B * Real.exp ((-β + ε r) * r)) :
    Tendsto (fun r => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (k r) (y r)) (-(k r))) atTop (𝓝 0) := by
  let N : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fun r => basisBracket (b r) (k r)
  have hnil : ∀ r, (N r) ^ (m + 1) = 0 :=
    fun r => basisBracket_pow_eq_zero (b r) hk (k r)
  have hN : ∀ᶠ r : ℝ in atTop, ‖N r‖ ≤ (C * A) * Real.exp ((α + ε r) * r) := by
    filter_upwards [hbound, hksize] with r hbr hr
    calc
      ‖N r‖ ≤ ‖basisBracket (b r)‖ * ‖k r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (A * Real.exp ((α + ε r) * r)) :=
        mul_le_mul hbr hr (norm_nonneg _) hC
      _ = _ := by ring
  have ht := nilpotent_exp_apply_tendsto_zero_of_subexponential_bounds
    N y hnil (mul_nonneg hC hA) hB hα hgap ε hε hN hysize
  apply ht.congr
  intro r
  have h := hconj r (k r) (y r) 1
  simpa only [one_smul] using h.symm

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DifferenceAmplitudeWord
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

theorem differenceParameters_surjective (m : ℕ) : Function.Surjective (differenceParameters m) := by
  intro x
  exact ⟨Fin.append x 0, by simp⟩

/-- The independent-difference parametrization retains the full rank proved
for the fixed generator word. -/
theorem differenceAmplitudeWord_surjective_fderiv {I : Type} [Fintype I] {n m c : ℕ}
    (a : DynkinCoefficients c 2) (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t₀ : Fin m → ℝ)
    (hs : Function.Surjective (fderiv ℝ (amplitudeWordEndpoint a letters p) t₀)) :
    Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters p) (Fin.append t₀ 0)) := by
  have hf : DifferentiableAt ℝ (amplitudeWordEndpoint a letters p) t₀ :=
    (((contDiff_amplitudeWordEndpoint (n := n) (q := 1) a letters).comp
      ((contDiff_const (c := p)).prodMk contDiff_id)).differentiable one_ne_zero) t₀
  have hf' : HasFDerivAt (amplitudeWordEndpoint a letters p)
      (fderiv ℝ (amplitudeWordEndpoint a letters p) t₀) (differenceParameters m (Fin.append t₀ 0)) := by
    simpa only [differenceParameters_append, sub_zero] using hf.hasFDerivAt
  have hd := hf'.comp (Fin.append t₀ 0) ((differenceParameters m).hasFDerivAt)
  change HasFDerivAt (differenceAmplitudeWordEndpoint a letters p) _ (Fin.append t₀ 0) at hd
  rw [hd.fderiv]
  exact hs.comp (differenceParameters_surjective m)

theorem exists_submersive_differenceAmplitudeWord {I J : Type} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → Fin n → ℝ) (b₀ : Basis J ℝ (Fin n → ℝ)) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j) :
    ∃ (m : ℕ) (letters : Fin m → I) (t₀ : Fin (m + m) → ℝ),
      differenceAmplitudeWordEndpoint a letters (B, X) t₀ = 0 ∧
      Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters (B, X)) t₀) := by
  obtain ⟨m, letters, t₀, hz, hs⟩ := exists_submersive_amplitudeWord a B hB hg hc X b₀ w₀ hw₀
  refine ⟨m, letters, Fin.append t₀ 0, ?_, differenceAmplitudeWord_surjective_fderiv a letters (B, X) t₀ hs⟩
  simpa only [differenceAmplitudeWordEndpoint, differenceParameters_append, sub_zero] using hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedCoordinateLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The limiting Lie law of maximizing word coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped BigOperators Topology

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

/-- Each normalized structure constant converges; the strict-degree terms
vanish and the degree-preserving terms stay unchanged. -/
theorem rescaled_structureCoefficient_tendsto
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (i j k : Fin n) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).repr
      ⁅exponentialRescaleBasis b cost r i, exponentialRescaleBasis b cost r j⁆ k)
      atTop (𝓝 (if cost i + cost j = cost k then b.repr ⁅b i, b j⁆ k else 0)) := by
  simp_rw [repr_exponentialRescaleBasis_bracket]
  by_cases hz : b.repr ⁅b i, b j⁆ k = 0
  · simp only [hz, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases he : cost i + cost j = cost k
  · simp only [he, sub_self, mul_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · have hlt : cost i + cost j - cost k < 0 := by
      have hw := hweight i j k hz
      exact sub_neg.mpr (lt_of_le_of_ne hw he)
    have ht := Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hlt).mpr tendsto_id)
    simpa [he, Function.comp_def] using ht.const_mul (b.repr ⁅b i, b j⁆ k)

/-- Convergence holds in the finite-dimensional normed space of bilinear
maps, so polynomial expressions in the group law converge on compacts. -/
theorem basisBracket_rescale_tendsto
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k) :
    Tendsto (fun r : ℝ => basisBracket (exponentialRescaleBasis b cost r)) atTop
      (𝓝 (gradedCoordinateBracket b cost)) := by
  let : ContinuousAdd ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    @IsTopologicalAddGroup.toContinuousAdd
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      inferInstance inferInstance inferInstance
  simp_rw [basisBracket_eq_coordinate_sum]
  unfold gradedCoordinateBracket
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact (rescaled_structureCoefficient_tendsto b cost hweight i j k).smul tendsto_const_nhds

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Maximality of the word-basis weight gives exactly the filtration
inequality on every nonzero structure constant. -/
theorem maximizing_word_basis_bracket_weight
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (i j l : Fin (finrank ℝ L))
    (hnz : (WordBasisSelections.basis X (boundedBracketWords k) β).repr
      ⁅WordBasisSelections.basis X (boundedBracketWords k) β i,
        WordBasisSelections.basis X (boundedBracketWords k) β j⁆ l ≠ 0) :
    bracketWordExponent s (β.val i) + bracketWordExponent s (β.val j) ≤
      bracketWordExponent s (β.val l) := by
  let S := boundedBracketWords (I := I) k
  let b := WordBasisSelections.basis X S β
  have hbr : ⁅b i, b j⁆ ≠ 0 := by
    intro hz
    exact hnz (by change b.repr ⁅b i, b j⁆ l = 0; rw [hz]; simp)
  let w : S := ⟨(β.val i : FreeMagma I) * β.val j, by
    apply (mem_boundedBracketWords _ _).mpr
    by_contra hn
    have hh := evalBracketWord_eq_zero_of_depth X hk
      ((β.val i : FreeMagma I) * β.val j) (Nat.le_of_not_lt hn)
    have he : evalBracketWord X ((β.val i : FreeMagma I) * β.val j) = ⁅b i, b j⁆ := by
      rw [evalBracketWord_mul]
      exact congrArg₂ (fun x y : L => ⁅x, y⁆)
        (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
    exact hbr (he.symm.trans hh)⟩
  have he : evalBracketWord X w = ⁅b i, b j⁆ := by
    change ⁅evalBracketWord X (β.val i), evalBracketWord X (β.val j)⁆ = _
    exact congrArg₂ (fun x y : L => ⁅x, y⁆)
      (WordBasisSelections.eval_words X S β i) (WordBasisSelections.eval_words X S β j)
  have hc : columnCoordinates (wordListCoordinates X S b₀) β.val w l = b.repr ⁅b i, b j⁆ l := by
    rw [columnCoordinates_eq_wordBasis_repr, he]
    rfl
  have hw := weight_le_of_nonzero_coordinate (wordListCoordinates X S b₀)
    (fun w => bracketWordExponent s w) β.val hβ w l
    (columnCoordinates (wordListCoordinates X S b₀) β.val w)
    (columnCoordinates_repr _ _ hβ.1 w) (by rw [hc]; exact hnz)
  simpa only [w, bracketWordExponent_mul] using hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GradedGeneratorLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generating vectors and group laws survive the graded limit -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

variable {L I : Type} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

theorem rescaled_generator_tendsto
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) (x : L)
    (hweight : ∀ j, b.repr x j ≠ 0 → s ≤ cost j) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).equivFun
      (Real.exp (r * s) • x)) atTop (𝓝 (gradedGenerator b cost s x)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).repr
    (Real.exp (r * s) • x) j) atTop (𝓝 (if s = cost j then b.repr x j else 0))
  simp_rw [repr_exponentialRescaleBasis_smul]
  by_cases hz : b.repr x j = 0
  · simp only [hz, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases he : s = cost j
  · simp only [he, sub_self, mul_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · have hlt : s - cost j < 0 := sub_neg.mpr (lt_of_le_of_ne (hweight j hz) he)
    have ht := Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hlt).mpr tendsto_id)
    simpa [he, Function.comp_def] using ht.const_mul (b.repr x j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialChartCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.rightNestedWord_length _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledSubmersiveScheme
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed submersive scheme for an actual sequence of rescalings

The subsequence and the word are selected from the actual coordinate laws,
before any good sheets or successful parameter sets are selected.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Filter Set
open scoped Topology

/-- Compact normalized laws retain their basis-word identities and hence a
submersive fixed word. This form keeps the compactness step independent of
the choice of a matrix realization. -/
theorem exists_submersive_scheme_of_normalized_sequence
    {I : Type} [Fintype I] {n c : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin n → FreeMagma I) (C : ℝ)
    (p : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ))
    (hp : ∀ k, p k ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C) :
    ∃ q ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C,
      ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (p ∘ u) atTop (𝓝 q) ∧
        ∃ (m : ℕ) (letters : Fin m → I) (t : Fin (m + m) → ℝ),
          differenceAmplitudeWordEndpoint a letters q t = 0 ∧
          Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters q) t) := by
  obtain ⟨q, hq, u, hu, hlim⟩ :=
    (isCompact_normalizedExponentialParameters a w (fun i => Pi.single i 1) C).tendsto_subseq hp
  have hwords (i : Fin n) : evalBilinearWord q.1 q.2 (w i) = Pi.basisFun ℝ (Fin n) i := by
    simpa only [Pi.basisFun_apply] using hq.1.1.2.2.2 i
  obtain ⟨m, letters, t, ht, hsurj⟩ := exists_submersive_differenceAmplitudeWord a q.1
    hq.1.1.2.2.1 hq.1.2 hq.2 q.2 (Pi.basisFun ℝ (Fin n)) w hwords
  exact ⟨q, hq, u, hu, hlim, m, letters, t, ht, hsurj⟩

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledWordSums
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential bounds for actual finite word expansions

The maximizing-basis exchange estimate controls every word in the finite
list. A common surplus or deficit in the coefficients passes to the norm
of the whole sum, uniformly over the selected maximizing basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- All words, rather than just the original letters, have uniformly bounded
coordinates after normalization by their own weight. -/
theorem exists_uniform_rescaled_word_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (cost : S → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ w : S,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => cost (β.val j)) r).equivFun
          (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound
    (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro cost β hβ r hr w
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r).repr
      (Real.exp (r * cost w) • evalBracketWord X w) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have h := hb cost β.val hβ w j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at h
  exact h

/-- A finite expansion with a common exponential margin retains that margin
in the actual normalized coordinate norm. The index may repeat words. -/
theorem norm_rescaled_word_sum_le
    {J : Type} [Fintype J]
    (X : I → L) (S : Finset (FreeMagma I))
    (b : Basis (Fin (finrank ℝ L)) ℝ L)
    (cost : S → ℝ) (r : ℝ) {C R θ : ℝ} (hR : 0 ≤ R)
    (hword : ∀ w : S, ‖b.equivFun
      (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C)
    (w : J → S) (a : J → ℝ)
    (ha : ∀ j, |a j| ≤ R * Real.exp (r * (cost (w j) + θ))) :
    ‖b.equivFun (∑ j, a j • evalBracketWord X (w j))‖ ≤
      (Fintype.card J : ℝ) * C * R * Real.exp (r * θ) := by
  have hcoef (j : J) : |a j * Real.exp (-(r * cost (w j)))| ≤
      R * Real.exp (r * θ) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (R * Real.exp (r * (cost (w j) + θ))) *
          Real.exp (-(r * cost (w j))) :=
        mul_le_mul_of_nonneg_right (ha j) (Real.exp_pos _).le
      _ = R * Real.exp (r * θ) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hterm (j : J) : ‖b.equivFun (a j • evalBracketWord X (w j))‖ ≤
      C * R * Real.exp (r * θ) := by
    have he : a j • evalBracketWord X (w j) =
        (a j * Real.exp (-(r * cost (w j)))) •
          (Real.exp (r * cost (w j)) • evalBracketWord X (w j)) := by
      rw [smul_smul, mul_assoc, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, mul_one]
    rw [he, map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (R * Real.exp (r * θ)) * C :=
        mul_le_mul (hcoef j) (hword (w j)) (norm_nonneg _)
          (mul_nonneg hR (Real.exp_pos _).le)
      _ = _ := by ring
  rw [map_sum]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] <;> ring))

end PolycyclicRecognition

end

end OAI
end

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

theorem exists_slow_sequence_subexponential_mass
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (mass : ℕ → ℕ → ℝ)
    (hmass : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ mass j n) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBoundSeq scale (fun n => mass (k n) n) := by
  have hgood (j : ℕ) : ∀ᶠ n in atTop,
      Real.exp (-(1 / ((j : ℝ) + 1)) * scale n) ≤ mass j n := by
    obtain ⟨c, hc, he⟩ := hmass j
    filter_upwards [((subexponential_lower_const hc).along_sequence hs)
      (1 / ((j : ℝ) + 1)) (by positivity), he] with n hn hm
    exact hn.trans hm
  obtain ⟨k, hk, he⟩ := exists_slow_sequence_selection _ hgood
  refine ⟨k, hk, ?_⟩
  intro ε hε
  have ht : Tendsto (fun n => 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  filter_upwards [he, ht.eventually (eventually_lt_nhds hε),
    hs.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hsmall hpos
  apply le_trans _ hn
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hsmall.le) hpos)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformSelection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform estimates from arbitrary parameter selections -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- To prove uniform convergence to a constant, it suffices to control every
choice of one parameter at each index. No topology on the parameter set is
needed. This lets a common word-coefficient envelope control whole families. -/
theorem tendstoUniformly_const_of_all_selections
    {ι Z V : Type} [PseudoMetricSpace V] {l : Filter ι}
    (F : ι → Z → V) (v : V)
    (h : ∀ z : ι → Z, Tendsto (fun i => F i (z i)) l (𝓝 v)) :
    TendstoUniformly F (fun _ => v) l := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_cases hz : Nonempty Z
  · let := hz
    let z : ι → Z := fun i => if hi : ∃ z, ¬dist v (F i z) < ε then
      Classical.choose hi else Classical.choice hz
    have hb (i : ι) (hi : ∃ z, ¬dist v (F i z) < ε) :
        ¬dist v (F i (z i)) < ε := by
      simpa only [z, dite_eq_left hi] using Classical.choose_spec hi
    have hp := (Metric.tendsto_nhds.mp (h z)) ε hε
    filter_upwards [hp] with i hi
    intro y
    by_contra hy
    exact hb i ⟨y, hy⟩ (by simpa only [dist_comm] using hi)
  · exact Eventually.of_forall (fun _ z => False.elim (hz ⟨z⟩))

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordInteriorSlack
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interior slack from actual finite word coefficients

A larger choice of the manuscript's free interior constant lets the
uniform nilpotent operator estimate absorb the enlarged suffix. No
coordinate growth estimate is assumed: both estimates follow from the
finite word expansions and maximizing-basis exchange.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology BigOperators

variable {I L G A : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The logarithm of the conjugate tends to zero in every maximizing
rescaled basis. This applies to the actual exponential product through
the faithful realization, with no new conjugation identity assumed. -/
theorem rescaled_word_conjugation_tendsto_zero
    [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {m k₀ c₀ : ℕ}
    (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hnil : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ)
    (β : ℝ → WordBasisSelections X (boundedBracketWords k₀))
    (hβ : ∀ r, IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) (β r).val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi K U : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (m : ℝ) * hi < c * lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (k u : ℝ → boundedBracketWords (I := I) k₀ → ℝ)
    (hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |k r w| ≤ K * Real.exp (r * ((1 + δ) * bracketWordExponent s w + ε r)))
    (hucoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |u r w| ≤ U * Real.exp (r * ((1 - c * δ) * bracketWordExponent s w + ε r))) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
      (fun i => bracketWordExponent s ((β r).val i)) r
    let x := fun r => (b r).equivFun
      (∑ w, k r w • evalBracketWord X w)
    let y := fun r => (b r).equivFun
      (∑ w, u r w • evalBracketWord X w)
    Tendsto (fun r => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (x r) (y r)) (-(x r))) atTop (𝓝 0) := by
  let S := boundedBracketWords (I := I) k₀
  let cost : S → ℝ := fun w => bracketWordExponent s w
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S (β r))
    (fun i => cost ((β r).val i)) r
  let x := fun r => (b r).equivFun (∑ w : S, k r w • evalBracketWord X w)
  let y := fun r => (b r).equivFun (∑ w : S, u r w • evalBracketWord X w)
  change Tendsto (fun r => dynkinProduct a (basisBracket (b r))
    (dynkinProduct a (basisBracket (b r)) (x r) (y r)) (-(x r))) atTop (𝓝 0)
  obtain ⟨C, hC, hword⟩ := exists_uniform_rescaled_word_bound X S b₀
  obtain ⟨D, hD, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound X hk b₀
  have hbnd : ∀ᶠ r : ℝ in atTop,
      ‖basisBracket (b r)‖ ≤ (finrank ℝ L : ℝ) ^ 2 * D := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact norm_basisBracket_le (b r) hD (hbracket s (β r) (hβ r) r hr)
  have hx : ∀ᶠ r : ℝ in atTop, ‖x r‖ ≤
      ((Fintype.card S : ℝ) * C * K) * Real.exp ((δ * hi + ε r) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hkcoeff] with r hr hkr
    have he (w : S) : |k r w| ≤ K * Real.exp (r * (cost w + (δ * hi + ε r))) := by
      apply (hkr w).trans
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have ht := mul_le_mul_of_nonneg_left (hcost w).2 hδ.le
      dsimp [cost]
      nlinarith
    have ht := norm_rescaled_word_sum_le X S (b r) cost r hK
      (hword cost (β r) (hβ r) r hr) id (k r) he
    simpa only [x, id_eq, mul_comm r] using ht
  have hy : ∀ᶠ r : ℝ in atTop, ‖y r‖ ≤
      ((Fintype.card S : ℝ) * C * U) * Real.exp ((-(c * δ * lo) + ε r) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hucoeff] with r hr hur
    have he (w : S) : |u r w| ≤ U * Real.exp (r * (cost w + (-(c * δ * lo) + ε r))) := by
      apply (hur w).trans
      apply mul_le_mul_of_nonneg_left _ hU
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have ht := mul_le_mul_of_nonneg_left (hcost w).1 (mul_nonneg hc hδ.le)
      dsimp [cost]
      nlinarith
    have ht := norm_rescaled_word_sum_le X S (b r) cost r hU
      (hword cost (β r) (hβ r) r hr) id (u r) he
    simpa only [y, id_eq, mul_comm r] using ht
  have hgap' : (m : ℝ) * (δ * hi) < c * δ * lo := by
    have ht := mul_lt_mul_of_pos_left hgap hδ
    nlinarith
  exact coordinate_conjugation_tendsto_zero b hnil a
    (fun r => basis_exponentialConjugationLaw (b r) Exp hinj hneg a hm j ρ hρ hmatch)
    x y (mul_nonneg (sq_nonneg _) hD)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hK)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hU)
    (mul_nonneg hδ.le hhi) hbnd hgap' ε hε hx hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformInteriorSlack
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interior slack uniform in the sampled chart position -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology BigOperators

variable {I L G A : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A common finite-word envelope gives uniform decay, even if the family
parameter has no regularity. In particular it controls every compact set of
sampled chart positions. -/
theorem rescaled_word_conjugation_tendstoUniformly
    {Z : Type} [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {m k₀ c₀ : ℕ}
    (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hnil : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ)
    (β : ℝ → WordBasisSelections X (boundedBracketWords k₀))
    (hβ : ∀ r, IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) (β r).val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi K U : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (m : ℝ) * hi < c * lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → boundedBracketWords (I := I) k₀ → ℝ)
    (u : ℝ → Z → boundedBracketWords (I := I) k₀ → ℝ)
    (hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |k r w| ≤ K * Real.exp (r * ((1 + δ) * bracketWordExponent s w + ε r)))
    (hucoeff : ∀ᶠ r : ℝ in atTop, ∀ z w,
      |u r z w| ≤ U * Real.exp (r * ((1 - c * δ) * bracketWordExponent s w + ε r))) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
      (fun i => bracketWordExponent s ((β r).val i)) r
    let x := fun r => (b r).equivFun
      (∑ w, k r w • evalBracketWord X w)
    let y := fun r z => (b r).equivFun
      (∑ w, u r z w • evalBracketWord X w)
    TendstoUniformly (fun r z => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (x r) (y r z)) (-(x r))) (fun _ => 0) atTop := by
  dsimp only
  apply tendstoUniformly_const_of_all_selections
  intro z
  exact rescaled_word_conjugation_tendsto_zero X hk hnil b₀ s β hβ
    Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi hK hU hcost hgap ε hε
    k (fun r => u r (z r)) hkcoeff
    (hucoeff.mono (fun r hr w => hr (z r) w))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BoxWordExpansion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite word coefficients of an actual enlarged box point -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Membership in a scaled word box supplies a finite expansion with a
common coefficient bound. Repetitions are harmless; the dimension factor
also covers them without any uniqueness requirement. -/
theorem exists_word_expansion_of_rescaled_norm_le
    {I L : Type} [LieRing L] [LieAlgebra ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R) (v : L)
    (hv : ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun i => cost (β.val i)) r).equivFun v‖ ≤ R) :
    ∃ a : S → ℝ,
      (∀ w, |a w| ≤ (finrank ℝ L : ℝ) * R * Real.exp (r * cost w)) ∧
      ∑ w, a w • evalBracketWord X w = v := by
  classical
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => cost (β.val i)) r
  let a : S → ℝ := fun w => ∑ i : Fin (finrank ℝ L),
    if β.val i = w then Real.exp (r * cost w) * b.repr v i else 0
  refine ⟨a, ?_, ?_⟩
  · intro w
    have hb (i : Fin (finrank ℝ L)) : |b.repr v i| ≤ R :=
      (norm_le_pi_norm (b.equivFun v) i).trans hv
    have hi (i : Fin (finrank ℝ L)) :
        |if β.val i = w then Real.exp (r * cost w) * b.repr v i else 0| ≤
          R * Real.exp (r * cost w) := by
      split_ifs
      · rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hb i) (Real.exp_pos _).le
      · simp only [abs_zero]
        positivity
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun i _ => hi i)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring)
  · calc
      (∑ w, a w • evalBracketWord X w) =
          ∑ i : Fin (finrank ℝ L),
            (Real.exp (r * cost (β.val i)) * b.repr v i) •
              evalBracketWord X (β.val i) := by
        simp only [a, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ i, b.repr v i • b i := by
        apply Finset.sum_congr rfl
        intro i _
        have hw := WordBasisSelections.eval_words X S β i
        change evalBracketWord X (β.val i) = _ at hw
        rw [hw]
        simp only [b, exponentialRescaleBasis, Basis.unitsSMul_apply,
          Units.smul_def, Units.val_mk0, smul_smul]
        rw [mul_comm]
      _ = v := b.sum_repr v

end PolycyclicRecognition

end

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_GradedFlowLimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of horizontal flows in graded coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Module
open scoped Topology

variable {n : ℕ}

/-- The polynomial flow depends continuously on its bracket and velocity
in the topology of uniform convergence on compact sets. -/
theorem continuous_dynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2) :
    Continuous (fun p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ) => dynkinFlowMap (n := n) a p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ) =>
    dynkinProduct a z.1.1 z.2.1 (z.2.2 • z.1.2))
  exact continuous_dynkinProduct (P := (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (Fin n → ℝ)) × ((Fin n → ℝ) × ℝ))
    a (fun z => z.1.1) (fun z => z.2.1) (fun z => z.2.2 • z.1.2)
    continuous_fst.fst continuous_snd.fst
    (continuous_snd.snd.smul continuous_fst.snd)

theorem dynkinFlowMap_tendsto {c : ℕ} (a : DynkinCoefficients c 2)
    {ι : Type} {l : Filter ι} {B : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {v : ι → (Fin n → ℝ)} {v₀ : (Fin n → ℝ)}
    (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => dynkinFlowMap (n := n) a (B i) (v i)) l (𝓝 (dynkinFlowMap (n := n) a B₀ v₀)) := by
  have hp : Tendsto (fun i => (B i, v i)) l (𝓝 (B₀, v₀)) := hB.prodMk_nhds hv
  simpa only [Function.comp_def] using
    ((continuous_dynkinFlowMap (n := n) a).tendsto (B₀, v₀)).comp hp

/-- Simultaneous convergence of base points and times on any fixed compact
set. This is the flow convergence used by chart profiles. -/
theorem dynkinFlowMap_tendstoUniformlyOn {c : ℕ} (a : DynkinCoefficients c 2)
    {ι : Type} {l : Filter ι} {B : ι → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {v : ι → (Fin n → ℝ)} {v₀ : (Fin n → ℝ)}
    (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀))
    {K : Set ((Fin n → ℝ) × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i z => dynkinProduct a (B i) z.1 (z.2 • v i))
      (fun z => dynkinProduct a B₀ z.1 (z.2 • v₀)) l K :=
  (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (dynkinFlowMap_tendsto (n := n) a hB hv)) K hK

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]

/-- Actual rescaled exponential lines tend to the line of the degree-one
part of their velocity, with the limiting graded multiplication. -/
theorem rescaled_horizontal_flow_tendstoUniformlyOn
    {c : ℕ} (a : DynkinCoefficients c 2) (b : Basis (Fin n) ℝ L)
    (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    {K : Set ((Fin n → ℝ) × ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun r z => dynkinProduct a (basisBracket (exponentialRescaleBasis b cost r))
        z.1 (z.2 • (exponentialRescaleBasis b cost r).equivFun (Real.exp r • v)))
      (fun z => dynkinProduct a (gradedCoordinateBracket b cost)
        z.1 (z.2 • gradedGenerator b cost 1 v)) atTop K := by
  apply dynkinFlowMap_tendstoUniformlyOn (n := n) a (basisBracket_rescale_tendsto b cost hweight)
    (v₀ := gradedGenerator b cost 1 v) ?_ hK
  simpa only [mul_one] using rescaled_generator_tendsto b cost 1 v hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateProfileFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coordinate flows used by the profile cutoffs -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Filter
open scoped Manifold Topology NNReal

/-- The full rescaled flow converges as a continuous map, so the cutoff
construction applies simultaneously to every compact time interval. -/
theorem rescaled_horizontal_flow_tendsto
    {L : Type} [LieRing L] [LieAlgebra ℝ L] {n c : ℕ}
    (a : DynkinCoefficients c 2) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j) :
    Tendsto (fun r => dynkinFlowMap a (basisBracket (exponentialRescaleBasis b cost r))
      ((exponentialRescaleBasis b cost r).equivFun (Real.exp r • v))) atTop
      (𝓝 (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v))) := by
  apply dynkinFlowMap_tendsto a (basisBracket_rescale_tendsto b cost hweight)
  simpa only [mul_one] using rescaled_generator_tendsto b cost 1 v hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateFlowProfileIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact increments for the actual polynomial horizontal flow -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped NNReal

theorem exp_basis_horizontal_flow
    {L D : Type} [LieRing L] [LieAlgebra ℝ L] [Group D] {n c : ℕ}
    (Exp : L → D) (b : Basis (Fin n) ℝ L) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r t : ℝ) (v : L) (z : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinFlowMap a (basisBracket b) (b.equivFun (r • v)) (z, t))) =
      Exp (b.equivFun.symm z) * Exp ((r * t) • v) := by
  change Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) z
    (t • b.equivFun (r • v)))) = _
  rw [exp_basis_dynkinProduct b Exp a hm]
  simp only [map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm t r]

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

/-- Uniform approximation on the fixed profile compact extends to the
actual varying flow. The only additional error tends to zero with that flow. -/
theorem good_profile_along_flow
    {U V W A ι : Type} {l : Filter ι} [TopologicalSpace U] [LocallyCompactSpace U]
    [TopologicalSpace V] [LocallyCompactSpace V] [NormedAddCommGroup W]
    (f : C(V, W)) (Ψ : ι → C(U, V)) (Ψ₀ : C(U, V))
    (hΨ : Tendsto Ψ l (𝓝 Ψ₀)) (K : Set U) (hK : IsCompact K)
    (Z : Set V) (hZ : ∀ᶠ r in l, ∀ u ∈ K, Ψ r u ∈ Z)
    (profile : ι → A → V → W) (good : ι → Set A) (ζ : ι → ℝ)
    (hgood : ∀ r a, a ∈ good r → ∀ z ∈ Z, ‖profile r a z - f z‖ ≤ ζ r)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in l, ∀ a ∈ good r, ∀ u ∈ K,
      ‖profile r a (Ψ r u) - f (Ψ₀ u)‖ ≤ ζ r + η := by
  have hf : Tendsto (fun r => f.comp (Ψ r)) l (𝓝 (f.comp Ψ₀)) :=
    (ContinuousMap.continuous_postcomp f).continuousAt.tendsto.comp hΨ
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hf) K hK
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) η hη
  filter_upwards [hZ, he] with r hr hclose
  intro a ha u huK
  calc
    ‖profile r a (Ψ r u) - f (Ψ₀ u)‖ ≤
        ‖profile r a (Ψ r u) - f (Ψ r u)‖ + ‖f (Ψ r u) - f (Ψ₀ u)‖ :=
      (by simpa only [dist_eq_norm] using dist_triangle (profile r a (Ψ r u)) (f (Ψ r u)) (f (Ψ₀ u)))
    _ ≤ ζ r + η := add_le_add (hgood r a ha _ (hr u huK))
      (by simpa only [ContinuousMap.comp_apply, dist_eq_norm, norm_sub_rev] using (hclose u huK).le)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledProfileLegs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical height bounds on the actual profile legs -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- Good profile values on the actual polynomial horizontal flow control
precisely the physical one-parameter leg at scale `exp s`. -/
theorem rescaled_profile_leg_bound
    {L D N G W : Type} [LieRing L] [LieAlgebra ℝ L]
    [Group D] [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n c : ℕ} (ExpD : L → D) (b : Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (ι : N → G) (κ : D →* G) (J : G → W) (x : G) (s : ℝ)
    (v : L) (z : Fin n → ℝ) (T : ℝ) (A : Set N)
    (flow : (Fin n → ℝ) × ℝ → Fin n → ℝ) (f : (Fin n → ℝ) → W) (ε : ℝ)
    (hgood : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledMapProfile J x (ι u) s (fun y => κ (ExpD (b.equivFun.symm y)))
          (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp s • v)) (z, t)) -
        f (flow (z, t))‖ ≤ ε) :
    ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) T,
      ‖J ((x * ι u * κ (ExpD (b.equivFun.symm z))) *
          κ (ExpD ((Real.exp s * t) • v))) - J x -
        Real.exp s • f (flow (z, t))‖ ≤ Real.exp s * ε := by
  intro u hu t ht
  have hh := height_bound_of_rescaled_profile J x (ι u) s
    (fun y => κ (ExpD (b.equivFun.symm y)))
    (dynkinFlowMap a (basisBracket b) (b.equivFun (Real.exp s • v)) (z, t))
    (f (flow (z, t))) (hgood u hu t ht)
  rw [exp_basis_horizontal_flow ExpD b a hm, map_mul] at hh
  simpa only [mul_assoc] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ScaleExtension
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending data from a strictly increasing sequence of scales

No regularity is imposed between the sampled scales. This bridge permits the
uniform real-scale estimates to be applied to the original sequence data.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem extendOnScales_apply {α : Type} {r : ℕ → ℝ} (hr : StrictMono r)
    (f : ℕ → α) (z : α) (n : ℕ) : extendOnScales r f z (r n) = f n := by
  classical
  unfold extendOnScales
  split_ifs with h
  · exact congrArg f (hr.injective h.choose_spec)
  · exact False.elim (h ⟨n, rfl⟩)

/-- Eventually true assertions on the indices hold at every sufficiently
large scale in the range; off that range the fixed default is used. -/
theorem eventually_extendOnScales {α : Type} {r : ℕ → ℝ} (hr : StrictMono r)
    (f : ℕ → α) (z : α) (P : ℝ → α → Prop)
    (hz : ∀ t, P t z) (hf : ∀ᶠ n in atTop, P (r n) (f n)) :
    ∀ᶠ t in atTop, P t (extendOnScales r f z t) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  filter_upwards [eventually_gt_atTop (r N)] with t ht
  unfold extendOnScales
  split_ifs with h
  · have hn : N ≤ h.choose := by
      by_contra hn
      have hlt : h.choose < N := Nat.lt_of_not_ge hn
      have hh := hr hlt
      rw [h.choose_spec] at hh
      exact (not_lt_of_ge ht.le) hh
    simpa only [h.choose_spec] using hN h.choose hn
  · exact hz t

theorem tendsto_extendOnScales {α : Type} [TopologicalSpace α] {r : ℕ → ℝ}
    (hr : StrictMono r) {f : ℕ → α} {z : α} (hf : Tendsto f atTop (𝓝 z)) :
    Tendsto (extendOnScales r f z) atTop (𝓝 z) := by
  apply tendsto_def.2
  intro U hU
  exact eventually_extendOnScales hr f z (fun _ x => x ∈ U)
    (fun _ => mem_of_mem_nhds hU) (hf.eventually hU)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceProfileSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good sheets selected along a converging sequence of profile laws -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

theorem exists_supported_good_sets_sequence
    {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {x : X} (hx : x ∈ (μ : Measure X).support)
    (U : ℕ → Set X) (hU : ∀ j, IsOpen (U j)) (hxU : ∀ j, x ∈ U j) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((μs n : Measure X) (U (k n))).toReal) := by
  exact exists_slow_sequence_subexponential_mass scale hs _ (fun j =>
    eventual_positive_mass_of_supported_weak_limit hμ hx (hU j) (hxU j))

theorem exists_good_sampled_observations_sequence
    {X A E : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A] [NormedAddCommGroup E]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → X)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    {f : X} (hf : f ∈ (ν : Measure X).support) (observe : C(X, E)) :
    ∃ (B : ℕ → Set A) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (B n)) ∧ (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((samples n : Measure A) (B n)).toReal) ∧
      ∀ n a, a ∈ B n → ‖observe (profile n a) - observe f‖ < ε n := by
  let U : ℕ → Set X := fun j => observe ⁻¹' Metric.ball (observe f) (1 / ((j : ℝ) + 1))
  have hU (j : ℕ) : IsOpen (U j) := Metric.isOpen_ball.preimage observe.continuous
  have hfU (j : ℕ) : f ∈ U j := by
    change dist (observe f) (observe f) < 1 / ((j : ℝ) + 1)
    simp only [dist_self]
    positivity
  obtain ⟨k, hk, hmass⟩ := exists_supported_good_sets_sequence scale hs hν hf U hU hfU
  let B := fun n => profile n ⁻¹' U (k n)
  let ε := fun n => 1 / ((k n : ℝ) + 1)
  refine ⟨B, ε, fun n => (hp n) (hU (k n)).measurableSet, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [ε]
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  · have heq (n : ℕ) :
        (ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure X) (U (k n)) =
          (samples n : Measure A) (B n) := by
      exact Measure.map_apply (hp n) (hU (k n)).measurableSet
    simpa only [heq] using hmass
  · intro n a ha
    change dist (observe (profile n a)) (observe f) < ε n at ha
    simpa only [dist_eq_norm] using ha

theorem exists_good_sampled_profiles_sequence
    {V W A : Type} [TopologicalSpace V] [NormedAddCommGroup W]
    [MeasurableSpace A] (S : Set C(V, W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (B : ℕ → Set A) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (B n)) ∧ (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun n => ((samples n : Measure A) (B n)).toReal) ∧
      ∀ n a, a ∈ B n → ∀ z ∈ K, ‖(profile n a).val z - f.val z‖ < ε n := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : C(K, V) := ⟨Subtype.val, continuous_subtype_val⟩
  let observe : C(S, C(K, W)) := ⟨fun g => g.val.comp incl,
    (ContinuousMap.continuous_precomp incl).comp continuous_subtype_val⟩
  obtain ⟨B, ε, hB, hε, hlim, hmass, hclose⟩ :=
    exists_good_sampled_observations_sequence scale hs samples profile hp ν hν hf observe
  refine ⟨B, ε, hB, hε, hlim, hmass, ?_⟩
  intro n a ha z hz
  have h := (observe (profile n a) - observe f).norm_coe_le_norm ⟨z, hz⟩
  exact h.trans_lt (hclose n a ha)

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

/-- The supported profile law gives shrinking errors on a prescribed
compact set and good subsets of the actual recurrence cells with relative
mass at least `exp(-o(scale))`. -/
theorem exists_good_cell_profiles_sequence
    {V W N : Type} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace N]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (μ : Measure N) (Q : ℕ → Set N) (hQ : ∀ n, MeasurableSet (Q n))
    (hQ0 : ∀ n, μ (Q n) ≠ 0) (hQfin : ∀ n, μ (Q n) ≠ ∞)
    (profile : ℕ → N → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n)) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (A : ℕ → Set N) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Q n) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) ∧
      (∀ᶠ n in atTop, 0 < (μ (A n)).toReal) ∧
      ∀ n a, a ∈ A n → ∀ z ∈ K, ‖(profile n a).val z - f.val z‖ < ε n := by
  obtain ⟨B, ε, hB, hε, hεlim, hmass, hgood⟩ := exists_good_sampled_profiles_sequence
    S K hK scale hs (fun n => cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n))
    profile hp ν hν hf
  let A := fun n => B n ∩ Q n
  have hmass' : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) := by
    simpa only [cellProbabilityMeasure_apply_toReal μ _ _ (hQ0 _) (hQfin _) (hB _)] using hmass
  refine ⟨A, ε, fun n => (hB n).inter (hQ n), fun _ => inter_subset_right,
    hε, hεlim, hmass', ?_, ?_⟩
  · filter_upwards [hmass'.eventually_pos] with n hn
    exact (div_pos_iff.mp hn).resolve_right (fun h => (ENNReal.toReal_nonneg).not_gt h.1)
      |>.1
  · intro n a ha
    exact hgood n a ha.1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactFlowNeighborhood
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One compact neighborhood for all sufficiently large coordinate flows -/

namespace PolycyclicRecognition

open Set Filter Metric
open scoped Topology

/-- Compact convergence of coordinate paths allows one compact cutoff to
contain the entire late family inside the prescribed open chart. -/
theorem exists_compact_eventual_flow_image
    {X Y ι : Type} [TopologicalSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {l : Filter ι} {F : ι → X → Y} {f : X → Y} {K : Set X} {U : Set Y}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hU : IsOpen U)
    (himage : f '' K ⊆ U) (hF : TendstoUniformlyOn F f l K) :
    ∃ Q : Set Y, IsCompact Q ∧ Q ⊆ U ∧ f '' K ⊆ Q ∧
      ∀ᶠ i in l, F i '' K ⊆ Q := by
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn hf
  obtain ⟨O, hO, hfO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hc hU himage
  obtain ⟨δ, hδ, hthick⟩ := hc.exists_thickening_subset_open hO hfO
  refine ⟨closure O, hOc, hOU, hfO.trans subset_closure, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) δ hδ] with i hi
  rintro y ⟨x, hx, rfl⟩
  apply subset_closure
  apply hthick
  exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, by simpa only [dist_comm] using hi x hx⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SequenceCellProfileSegment
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting good sampled sheets for an entire horizontal segment -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- A supported weak profile limit gives one slowly improving family of
good sheets on a compact neighborhood of the entire actual late segment.
The endpoint scheme can be fixed before this selection. -/
theorem exists_good_cell_profiles_along_segment_sequence
    {V W A : Type} [MetricSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure A) (cells : ℕ → Set A) (hcells : ∀ n, MeasurableSet (cells n))
    (hcell0 : ∀ n, μ (cells n) ≠ 0) (hcellfin : ∀ n, μ (cells n) ≠ ∞)
    (profile : ℕ → A → S)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (cellProbabilityMeasure μ (cells r) (hcell0 r) (hcellfin r)) (f := (profile r)) (by first | exact (hp r).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support)
    (Ψ : ℕ → C(V × ℝ, V)) (Ψ₀ : C(V × ℝ, V))
    (hΨ : Tendsto Ψ atTop (𝓝 Ψ₀)) (z : V) (T : ℝ)
    (U : Set V) (hU : IsOpen U) (hseg : ∀ t ∈ Icc 0 T, Ψ₀ (z, t) ∈ U) :
    ∃ (Q : Set V) (B : ℕ → Set A) (ζ : ℕ → ℝ),
      IsCompact Q ∧ Q ⊆ U ∧
      (∀ᶠ r in atTop, ∀ t ∈ Icc 0 T, Ψ r (z, t) ∈ Q) ∧
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, B r ⊆ cells r) ∧ (∀ r, 0 < ζ r) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (μ (B r)).toReal / (μ (cells r)).toReal) ∧
      (∀ᶠ r in atTop, 0 < (μ (B r)).toReal) ∧
      (∀ r a, a ∈ B r → ∀ w ∈ Q, ‖(profile r a).val w - f.val w‖ < ζ r) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ a ∈ B r, ∀ t ∈ Icc 0 T,
        ‖(profile r a).val (Ψ r (z, t)) - f.val (Ψ₀ (z, t))‖ ≤ ζ r + η := by
  let K := ({z} : Set V) ×ˢ Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have himage : Ψ₀ '' K ⊆ U := by
    rintro _ ⟨⟨w, t⟩, ⟨hw, ht⟩, rfl⟩
    have hwz : w = z := mem_singleton_iff.mp hw
    subst w
    exact hseg t ht
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hΨ) K hK
  obtain ⟨Q, hQ, hQU, _, hlate⟩ := exists_compact_eventual_flow_image hK
    Ψ₀.continuous.continuousOn hU himage hunif
  obtain ⟨B, ζ, hB, hBcell, hζ, hζlim, hmass, hpos, hgood⟩ :=
    exists_good_cell_profiles_sequence S Q hQ scale hscale μ cells hcells hcell0 hcellfin profile hp ν hν hf
  have hZ : ∀ᶠ r in atTop, ∀ u ∈ K, Ψ r u ∈ Q := by
    filter_upwards [hlate] with r hr u hu
    exact hr (mem_image_of_mem _ hu)
  refine ⟨Q, B, ζ, hQ, hQU, ?_, hB, hBcell, hζ, hζlim, hmass, hpos, hgood, ?_⟩
  · filter_upwards [hZ] with r hr t ht
    exact hr (z, t) ⟨mem_singleton z, ht⟩
  · intro η hη
    have hh := good_profile_along_flow f.val Ψ Ψ₀ hΨ K hK Q hZ
      (fun r a => (profile r a).val) B ζ (fun r a ha w hw => (hgood r a ha w hw).le) hη
    filter_upwards [hh] with r hr a ha t ht
    exact hr a ha (z, t) ⟨mem_singleton z, ht⟩

end PolycyclicRecognition

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
theorem weightSupport_mono {E F : Set W} (hE : IsCompact E) (hn : E.Nonempty)
    (hF : IsCompact F) (hEF : E ⊆ F) (i : I) :
    D.weightSupport E i ≤ D.weightSupport F i := by
  obtain ⟨x, hx, heq⟩ := D.exists_weightSupport_point hE hn i
  rw [heq]
  exact D.weight_le_weightSupport hF (hEF hx) i

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslatedBoxMass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume ratios for translated exponential boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G : Type} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- Enlarging the radius of a fixed exponential box multiplies its Haar
volume by exactly the corresponding power, independently of the scale. -/
theorem exponential_box_radius_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal (R ^ n) *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b R hR,
    exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b 1 zero_le_one]
  rw [exponential_basis_subset_measure e Exp chart hchart b₀ b,
    exponential_basis_subset_measure e Exp chart hchart b₀ b]
  rw [Real.volume_Icc_pi, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_one]
  rw [ENNReal.ofReal_pow hR, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
  ring

/-- The conjugated increment lies in a small box; hence the translated
source box times that increment lies in the translated product box. -/
theorem translated_box_increment_mem {G : Type} [Group G]
    {B R : Set G} (hprod : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ R)
    (k s : G) (hs : k * s * k⁻¹ ∈ B) {x : G}
    (hx : x ∈ (fun y => y * k) '' B) :
    x * s ∈ (fun y => y * k) '' R := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y * (k * s * k⁻¹), hprod y hy _ hs, ?_⟩
  group

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_UniformIntervalSamples
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interval sampling has a fixed density on the full parameter cube -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

theorem uniformIntervalLaw_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (uniformIntervalLaw R) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_closedBall, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hR))
  · rw [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed submersive words in the actual Cartan box coordinates -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The endpoint word is fixed from the limiting genuine Cartan box law.
The only external inputs are the stated exponential realization and Haar
chart, which provide the faithful realization and injective exponential. -/
theorem exists_box_normalized_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {c : ℕ} (aN : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b)
      (M.boxCost T hunimod eW E) β.val)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      rescaledLieData M.letter M.wordList β ((M.supportIn T hunimod eW).weightSupport E) r ∈
        normalizedExponentialParameters aN
          (fun i => (β.val i : FreeMagma (Fin M.letterCount))) (fun i => Pi.single i 1) C := by
  obtain ⟨d, hd, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin d) (Fin d) ℝ)ˣ =>
      (u : Matrix (Fin d) (Fin d) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hinj : Function.Injective (F.ExpN ∘ F.N.equiv) :=
    ((funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective).injective
  have hmul (x y : cartanRootIdeal H) :
      (F.ExpN ∘ F.N.equiv) (finiteDynkinPolynomial aN ![x, y]) =
        (F.ExpN ∘ F.N.equiv) x * (F.ExpN ∘ F.N.equiv) y :=
    model_binary_dynkin F.N.equiv F.ExpN aN hm x y
  obtain ⟨C, hC, hb⟩ := exists_rescaledExponentialData_bound M.letter M.bound_zero M.letter_mem_wordList b
    (F.ExpN ∘ F.N.equiv) hinj (by simp [F.isExpN.map_zero])
    (fun x => by simp [F.isExpN.map_neg])
    (fun x s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv x) s t)
    aN hmul (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun x => by
      change ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = _
      rw [F.compatibleN, hmatch]
      rfl)

  exact ⟨C, hC, fun r hr => hb ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr⟩


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorCharts
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual factor-chart continuity and the exponential Cartan action -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Manifold

set_option maxHeartbeats 1000000 in
/-- The published nilpotent exponential chart makes every identified
linear coordinate chart continuous. -/
theorem continuous_model_exp_coordinates
    {E N L : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N] [LieRing L] [LieAlgebra ℝ L]
    (haar : NilpotentExponentialHaarInput E N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) N))
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    Continuous (fun z => Exp (e (b.equivFun.symm z))) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  have hc := chart.continuous.comp
    ((b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.continuous)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  change Exp (e (b.equivFun.symm z)) = chart ((b.map e.toLinearEquiv).equivFun.symm z)
  rw [hchart]
  rfl

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCellFlowLegs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported sampled profiles control the actual large-scale flow legs -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Combine the slow good-sheet selection, proved graded-flow convergence,
and the exact exponential-coordinate identity. The conclusion is expressed
at physical scale `r`, along the original one-parameter subgroup. -/
theorem exists_good_cell_rescaled_flow_legs_sequence
    {L D N G W : Type} [LieRing L] [LieAlgebra ℝ L]
    [Group D] [Group G] [MeasurableSpace N]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n c : ℕ}
    (ExpD : L → D) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, ExpD (finiteDynkinPolynomial a ![x, y]) = ExpD x * ExpD y)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (v : L) (hv : ∀ j, b.repr v j ≠ 0 → 1 ≤ cost j)
    (ι : ℕ → N → G) (κ : D →* G) (J : ℕ → G → W) (x : ℕ → G)
    (S : Set C((Fin n → ℝ), W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (μ : Measure N) (cells : ℕ → Set N) (hcells : ∀ n, MeasurableSet (cells n))
    (hcell0 : ∀ n, μ (cells n) ≠ 0) (hcellfin : ∀ n, μ (cells n) ≠ ∞)
    (profile : ℕ → N → S)
    (hp : ∀ r, Measurable (profile r)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun r => ProbabilityMeasure.map (cellProbabilityMeasure μ (cells r) (hcell0 r) (hcellfin r)) (f := (profile r)) (by first | exact (hp r).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (hactual : ∀ r u, u ∈ cells r → ∀ z, (profile r u).val z =
      rescaledMapProfile (J r) (x r) (ι r u) (max (Real.log (scale r)) 0)
        (fun z => κ (ExpD ((exponentialRescaleBasis b cost (max (Real.log (scale r)) 0)).equivFun.symm z))) z)
    (z : Fin n → ℝ) (T : ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hseg : ∀ t ∈ Icc 0 T,
      dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t) ∈ U)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (B : ℕ → Set N) (ζ : ℕ → ℝ),
      (∀ r, MeasurableSet (B r)) ∧ (∀ r, B r ⊆ cells r) ∧ (∀ r, 0 < ζ r) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (μ (B r)).toReal / (μ (cells r)).toReal) ∧
      (∀ r, 0 < (μ (B r)).toReal) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ B r, ∀ t ∈ Icc 0 T,
        ‖J r ((x r * ι r u * κ (ExpD
            ((exponentialRescaleBasis b cost (max (Real.log (scale r)) 0)).equivFun.symm z))) *
              κ (ExpD ((scale r * t) • v))) - J r (x r) -
          scale r • f.val (dynkinFlowMap a (gradedCoordinateBracket b cost)
            (gradedGenerator b cost 1 v) (z, t))‖ ≤ scale r * (ζ r + η) := by
  let logscale := fun r : ℕ => max (Real.log (scale r)) 0
  let basis := fun r => exponentialRescaleBasis b cost (logscale r)
  let Ψ := fun r => dynkinFlowMap a (basisBracket (basis r))
    ((basis r).equivFun (Real.exp (logscale r) • v))
  let Ψ₀ := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  have hlogscale : Tendsto logscale atTop atTop :=
    tendsto_atTop_mono (fun r => le_max_left (Real.log (scale r)) 0)
      (Real.tendsto_log_atTop.comp hscale)
  have hΨ : Tendsto Ψ atTop (𝓝 Ψ₀) :=
    (rescaled_horizontal_flow_tendsto a b cost hweight v hv).comp hlogscale
  obtain ⟨Q, B, ζ, _, _, _, hB, hBcell, hζ, hζlim, hmass, hpos, _, hgood⟩ :=
    exists_good_cell_profiles_along_segment_sequence S scale hscale μ cells hcells hcell0 hcellfin profile hp ν hν hf Ψ Ψ₀ hΨ z T U hU hseg
  classical
  let B' := fun n => if 0 < (μ (B n)).toReal then B n else cells n
  have hsame : ∀ᶠ n in atTop, B' n = B n :=
    hpos.mono (fun n hn => ite_eq_left hn)
  have hB' (n : ℕ) : MeasurableSet (B' n) := by
    dsimp [B']; split_ifs
    · exact hB n
    · exact hcells n
  have hsub (n : ℕ) : B' n ⊆ cells n := by
    dsimp [B']; split_ifs
    · exact hBcell n
    · exact subset_rfl
  have hpos' (n : ℕ) : 0 < (μ (B' n)).toReal := by
    dsimp [B']; split_ifs with h
    · exact h
    · exact ENNReal.toReal_pos (hcell0 n) (hcellfin n)
  have hmass' : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (B' n)).toReal / (μ (cells n)).toReal) := by
    apply hmass.mono
    filter_upwards [hsame] with n hn
    rw [hn]
  refine ⟨B', ζ, hB', hsub, hζ, hζlim, hmass', hpos', ?_⟩
  intro η hη
  filter_upwards [hgood η hη, hscale.eventually (eventually_ge_atTop (1 : ℝ)), hsame] with r hr hr1 heq
  rw [heq]
  have he : Real.exp (logscale r) = scale r := by
    dsimp [logscale]
    rw [max_eq_left (Real.log_nonneg hr1), Real.exp_log (lt_of_lt_of_le zero_lt_one hr1)]
  have hg : ∀ u ∈ B r, ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledMapProfile (J r) (x r) (ι r u) (logscale r)
          (fun y => κ (ExpD ((basis r).equivFun.symm y))) (Ψ r (z, t)) -
        f.val (Ψ₀ (z, t))‖ ≤ ζ r + η := by
    intro u hu t ht
    simpa only [hactual r u (hBcell r hu)] using hr u hu t ht
  have hh := rescaled_profile_leg_bound ExpD (basis r) a hm (ι r) κ (J r) (x r) (logscale r)
    v z T (B r) Ψ₀ f.val (ζ r + η) hg
  simpa only [he] using hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGoodCellLegs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good physical legs on the actual translated Cartan Haar cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Fintype I] [DecidableEq I]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] in
/-- A supported coordinate profile supplies actual good group sheets. Their
relative Haar mass, their positivity and every physical segment leg are
proved together, with the original translated cell retained. -/
theorem exists_good_cartan_cell_legs_sequence
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (k : ℕ → cartanRootIdeal H)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ u v, F.ExpD (finiteDynkinPolynomial aD ![u, v]) = F.ExpD u * F.ExpD v)
    (J : ℕ → G → W) (x : ℕ → G)
    (C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) (hC : MeasurableSet C)
    (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ∞)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume C hC0 hCfin) (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν))
    (v : H) (z : Fin (finrank ℝ H) → ℝ) (T₀ : ℝ)
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hseg : ∀ t ∈ Icc 0 T₀,
      dynkinFlowMap aD
        (gradedCoordinateBracket (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)))
        (gradedGenerator (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) 1 v) (z, t) ∈ U)
    (hactual : ∀ n y, y ∈ C → ∀ w, (profile n y).val w =
      rescaledMapProfile (J n) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
            ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
          F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun w => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm w)))) w)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let sample := fun n y => F.ExpN (F.N.equiv
      ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y)) * F.ExpN (F.N.equiv (k n))
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    ∃ (A : ℕ → Set F.N.carrier) (ζ : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ sample n '' C) ∧
      (∀ n, 0 < (μ (A n)).toReal) ∧ (∀ n, 0 < ζ n) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ A n, ∀ t ∈ Icc 0 T₀,
        ‖J n ((x n * F.inclusionN u * F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis b cost (max (Real.log (scale n)) 0)).equivFun.symm z)))) *
              F.inclusionD (F.ExpD (F.D.equiv ((scale n * t) • v)))) -
            J n (x n) - scale n • f.val
              (dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))‖ ≤
          scale n * (ζ n + η) := by
  dsimp only
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let sample := fun n y => F.ExpN (F.N.equiv
    ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y)) * F.ExpN (F.N.equiv (k n))
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (βD.val j)
  obtain ⟨B, ζ, hB, hBC, hζ, hζlim, hmass, hBpos, hlegs⟩ :=
    exists_good_cell_rescaled_flow_legs_sequence (F.ExpD ∘ F.D.equiv) b cost aD
      (model_binary_dynkin F.D.equiv F.ExpD aD hmD) hweight v hv
      (fun n y => F.inclusionN (sample n y)) F.inclusionD J x S scale hscale
      volume (fun _ => C) (fun _ => hC) (fun _ => hC0) (fun _ => hCfin)
      profile hp ν hν (by simpa only [sample, b, cost, Function.comp_apply, map_mul] using hactual) z T₀ U hU hseg hf
  let A := fun n => sample n '' B n
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  have hratio (n : ℕ) : (μ (A n)).toReal / (μ (sample n '' C)).toReal =
      (volume (B n)).toReal / (volume C).toReal :=
    translated_exponential_cell_ratio haarN F.N.equiv hnil F.ExpN F.isExpN chartN hchartN
      M.letter M.wordList b₀ β (M.boxCost T hunimod eW E) (scale n)
      (F.ExpN (F.N.equiv (k n))) (B n) C
  refine ⟨A, ζ, ?_, fun n => image_mono (hBC n), ?_, hζ, hζlim, ?_, ?_⟩
  · intro n
    exact (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β (scale n)) (F.ExpN (F.N.equiv (k n)))).measurableSet_image.mpr (hB n)
  · intro n
    have hh := div_pos (hBpos n) (ENNReal.toReal_pos hC0 hCfin)
    rw [← hratio n] at hh
    exact (div_pos_iff.mp hh).resolve_right (fun h => ENNReal.toReal_nonneg.not_gt h.1) |>.1
  · change HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal)
    simpa only [hratio] using hmass
  · intro η hη
    filter_upwards [hlegs η hη] with n hn u hu t ht
    obtain ⟨y, hy, rfl⟩ := hu
    exact hn y hy t ht

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRecurrenceBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed denominator bound for the recurrence boxes -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
include hExp haar dynkin in
/-- Once the conjugated increment is in the unit normalized box, a single
fixed enlargement controls every recurrence denominator. Its volume ratio
is independent of the template, scale, suffix and increment law. -/
theorem exists_recurrence_box_enlargement
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (E : Set W) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val → ∀ r : ℝ, 0 ≤ r →
      let B := M.groupBox T hunimod eW (Exp ∘ eN) E β r
      let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
      (∀ k s : N, k * s * k⁻¹ ∈ B 1 →
        ∀ x ∈ (fun y => y * k) '' B 1, x * s ∈ (fun y => y * k) '' B R) ∧
      ∀ k : N, μ ((fun y => y * k) '' B R) =
        ENNReal.ofReal (R ^ finrank ℝ (cartanRootIdeal H)) * μ ((fun y => y * k) '' B 1) := by
  obtain ⟨C, hC, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW eN Exp hExp dynkin b₀
  let R := 1 + C * (3 : ℝ) ^ M.bound * (2 : ℝ) ^ M.bound
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_right (by positivity)
  refine ⟨R, hR, ?_⟩
  intro E β hβ r hr
  dsimp only
  let B := M.groupBox T hunimod eW (Exp ∘ eN) E β r
  have hbinary : ∀ x ∈ B 1, ∀ y ∈ B 1, x * y ∈ B R := by
    intro x hx y hy
    have hh := hprod E β hβ r hr 2 1 zero_le_one ![x, y] (by
      intro i
      fin_cases i
      · exact hx
      · exact hy)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Matrix.cons_val_zero, mul_one] at hh
    obtain ⟨z, hz, hb⟩ := hh
    refine ⟨z, hz, hb.trans ?_⟩
    dsimp [R]
    norm_num
  constructor
  · intro k s hs x hx
    exact translated_box_increment_mem hbinary k s hs hx
  · let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
    have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
      (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar eN hnil Exp hExp b₀
    obtain ⟨⟨chart, hc⟩, _⟩ := haar.2 Exp hExp (eN.nilpotent_iff_equiv_nilpotent.mp hnil)
    intro k
    change μ ((fun y => y * k) '' B R) = _
    rw [measure_image_mul_right μ, measure_image_mul_right μ]
    exact exponential_box_radius_measure eN Exp chart hc b₀
      (M.boxBasis T hunimod eW E β r) (zero_le_one.trans hR)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSlack
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interior slack for the actual bounded root intervals -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Topology BigOperators

variable {I L G A : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every bounded interval in an interior root direction remains in the
unit normalized box after conjugation by the enlarged suffix. The actual
finite-word envelope is constructed from the root and suffix coordinates. -/
theorem root_interval_conjugation_mem_box
    [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {k₀ c₀ : ℕ} (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hletters : ∀ i, FreeMagma.of i ∈ boundedBracketWords (I := I) k₀)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s q : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k₀))
    (hβ : IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (k₀ : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * s i)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → L)
    (hkbox : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k₀) β)
        (fun i => (1 + δ) * bracketWordExponent s (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r)) :
    ∀ᶠ r in atTop, ∀ i t, |t| ≤ R →
      Exp (k r) * Exp ((t * Real.exp (r * q i)) • X i) * (Exp (k r))⁻¹ ∈
        exponentialCoordinateBox Exp
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k₀) β)
            (fun i => bracketWordExponent s (β.val i)) r) 1 := by
  classical
  let S := boundedBracketWords (I := I) k₀
  let cost : S → ℝ := fun w => bracketWordExponent s w
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => cost (β.val i)) r
  let bk := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => (1 + δ) * cost (β.val i)) r
  have hex (r : ℝ) := exists_word_expansion_of_rescaled_norm_le X S β
    (fun w => (1 + δ) * cost w) r (norm_nonneg ((bk r).equivFun (k r))) (k r) le_rfl
  choose ak hak hkeq using hex
  have hak' : ∀ᶠ r in atTop, ∀ w,
      |ak r w| ≤ (finrank ℝ L : ℝ) * Real.exp (r * ((1 + δ) * cost w + ε r)) := by
    filter_upwards [hkbox] with r hr w
    apply (hak r w).trans
    calc
      _ ≤ (finrank ℝ L : ℝ) * Real.exp (r * ε r) *
          Real.exp (r * ((1 + δ) * cost w)) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Z := {z : I × ℝ // |z.2| ≤ R}
  let letter (i : I) : S := ⟨FreeMagma.of i, hletters i⟩
  let au (r : ℝ) (z : Z) (w : S) :=
    if w = letter z.val.1 then z.val.2 * Real.exp (r * q z.val.1) else 0
  have hau : ∀ᶠ r in atTop, ∀ z w,
      |au r z w| ≤ R * Real.exp (r * ((1 - c * δ) * cost w + ε r)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr z w
    by_cases hw : w = letter z.val.1
    · subst w
      simp only [au, ite_eq_left rfl, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul z.property _ (Real.exp_pos _).le hR
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have he : cost (letter z.val.1) = s z.val.1 := by
        simp only [cost, letter, bracketWordExponent_of]
      rw [he]
      exact (hq _).trans (le_add_of_nonneg_right (hεpos r))
    · simp only [au, ite_eq_right hw, abs_zero]
      positivity
  have hueq (r : ℝ) (z : Z) :
      ∑ w, au r z w • evalBracketWord X w =
        (z.val.2 * Real.exp (r * q z.val.1)) • X z.val.1 := by
    simp [au, letter]
  have hnil : lowerCentralSeries ℝ L L (k₀ + 1) = ⊥ := by
    rw [lowerCentralSeries_succ, hk]
    simp
  have hu := rescaled_word_conjugation_tendstoUniformly X hk hnil b₀ s
    (fun _ => β) (fun _ => hβ) Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi
    (Nat.cast_nonneg _) hR hcost hgap ε hε ak au hak' hau
  have hsmall := (Metric.tendstoUniformly_iff.mp hu) 1 zero_lt_one
  filter_upwards [hsmall] with r hr i t ht
  let z : Z := ⟨(i, t), ht⟩
  let v := dynkinProduct a (basisBracket (b r))
    (dynkinProduct a (basisBracket (b r)) ((b r).equivFun (k r))
      ((b r).equivFun ((t * Real.exp (r * q i)) • X i))) (-((b r).equivFun (k r)))
  refine ⟨(b r).equivFun.symm v, ?_, ?_⟩
  · simp only [v, exp_basis_dynkinProduct (b r) Exp a hm,
      LinearEquiv.symm_apply_apply, map_neg, hneg]
  · rw [LinearEquiv.apply_symm_apply]
    have hh := hr z
    change dist 0 (dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r))
        ((b r).equivFun (∑ w, ak r w • evalBracketWord X w))
        ((b r).equivFun (∑ w, au r z w • evalBracketWord X w)))
      (-((b r).equivFun (∑ w, ak r w • evalBracketWord X w)))) < 1 at hh
    rw [hkeq, hueq] at hh
    simpa only [v, z, dist_zero_left] using hh.le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRootIntervalSlack
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-interval recurrence slack in the actual Cartan factor -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The previously published linear realization supplies the actual
conjugation law. All interval and enlarged-suffix decay estimates are proved
from the finite root-word model. -/
theorem root_interval_slack_of_published_realization
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r)) :
    ∀ᶠ r in atTop, ∀ i t, |t| ≤ R →
      F.ExpN (F.N.equiv (k r)) *
        F.ExpN (F.N.equiv ((t * Real.exp (r * q i)) • M.letter i)) *
          (F.ExpN (F.N.equiv (k r)))⁻¹ ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1 := by
  obtain ⟨m, hmpos, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective (F.ExpN ∘ F.N.equiv) :=
    (funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective
  have hletters (i : Fin M.letterCount) : FreeMagma.of i ∈ M.wordList := by
    apply M.mem_wordList_of_eval_ne_zero
    simp only [evalBracketWord_of]
    intro he
    have hh := M.letter_quotient i
    rw [he, map_zero] at hh
    exact M.abelianBasis.ne_zero i hh.symm
  apply root_interval_conjugation_mem_box M.letter M.bound_zero hletters b₀
    ((M.supportIn T hunimod eW).weightSupport E) q β hβ
    (F.ExpN ∘ F.N.equiv) hbij.injective (fun x => by simp [F.isExpN.map_neg])
    aN (model_binary_dynkin F.N.equiv F.ExpN aN hm)
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) _ hδ hc hhi hR hcost hgap hq ε hεpos hε k hk
  intro x
  change ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = _
  rw [F.compatibleN, hmatch]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent interval laws for the root increments -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {L N I : Type} [AddCommGroup L] [Module ℝ L] [Group N]

omit [Group N] in
theorem rootIntervalSample_letter (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (j : Fin m) (t : ℝ) :
    rootIntervalSample Exp letters X s r j.val t =
      Exp (t • (Real.exp (r * s (letters j)) • X (letters j))) := by
  simp [rootIntervalSample, rootIntervalDirection, j.isLt]

/-- Two independent interval samples differ by the single intended root
increment. There is no need to retain a profile at their intermediate product. -/
theorem rootIntervalSample_sub (Exp : L → N)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ (v : L) (u t : ℝ), Exp ((u + t) • v) = Exp (u • v) * Exp (t • v))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r : ℝ) (j : ℕ) (u t : ℝ) :
    rootIntervalSample Exp letters X s r j u * (rootIntervalSample Exp letters X s r j t)⁻¹ =
      rootIntervalSample Exp letters X s r j (u - t) := by
  unfold rootIntervalSample
  rw [← hneg, ← neg_smul, ← hadd, sub_eq_add_neg]

variable [MeasurableSpace N]

omit [Group N] in
/-- These are pushforward laws of the original independent uniform samples. -/
theorem measurePreserving_rootIntervalSample [TopologicalSpace N] [BorelSpace N]
    (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ)
    (j : ℕ) :
    MeasurePreserving (rootIntervalSample Exp letters X s r j) (uniformIntervalLaw R)
      (rootIntervalLaw Exp letters X s r R j) := by
  exact ⟨(hcont _).measurable, rfl⟩

omit [Group N] in
theorem rootIntervalLaw_isProbability [TopologicalSpace N] [BorelSpace N] (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v))) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    IsProbabilityMeasure (rootIntervalLaw Exp letters X s r R j) := by
  let := uniformIntervalLaw_isProbability hR
  unfold rootIntervalLaw
  exact Measure.isProbabilityMeasure_map (hcont _).measurable.aemeasurable

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalSupports
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact supports of the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type} [AddCommGroup L] [Module ℝ L]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

omit [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem isCompact_rootIntervalSupport (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) :
    IsCompact (rootIntervalSupport Exp letters X s r R j) :=
  (isCompact_closedBall (0 : ℝ) R).image (hcont _)

theorem rootIntervalLaw_ae_mem_support (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) :
    ∀ᵐ u ∂rootIntervalLaw Exp letters X s r R j,
      u ∈ rootIntervalSupport Exp letters X s r R j := by
  apply (ae_map_iff (hcont _).measurable.aemeasurable
    (isCompact_rootIntervalSupport Exp hcont letters X s r R j).measurableSet).mpr
  exact (ProbabilityTheory.ae_cond_mem measurableSet_closedBall).mono
    (fun t ht => mem_image_of_mem _ ht)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanIntervalDenominator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The compact support of every original interval law fits into one fixed
translated enlarged box. Its exact Haar-volume ratio is independent of scale. -/
theorem exists_interval_recurrence_denominator
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    {m : ℕ} (letters : Fin m → Fin M.letterCount) :
    ∃ D : ℝ, 1 ≤ D ∧
      let μ := MeasureTheory.Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm)
        MeasureTheory.volume
      ∀ᶠ r in atTop,
        let k₀ := F.ExpN (F.N.equiv (k r))
        let Q := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
        let Q' := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r D
        (∀ j : Fin m, ∀ x ∈ Q,
          ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q r R j.val,
            x * u ∈ Q') ∧
        μ Q' = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ Q := by
  have hnilN : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
      (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) M.bound = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq M.bound F.N.equiv.surjective, M.bound_zero]
    simp
  obtain ⟨aN, _, hprod⟩ := dynkinN F.ExpN F.isExpN M.bound hnilN 2
  have hm (x y : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) :
      F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y := by
    simpa [List.ofFn_succ] using (hprod ![x, y]).symm
  have hslack := M.root_interval_slack_of_published_realization T F hunimod eW
    hExpG realize haarN b₀ E β q hβ hδ hc hhi hR hcost hgap hq aN hm ε hεpos hε k hk
  obtain ⟨D, hD, hdenom⟩ := M.exists_recurrence_box_enlargement T hunimod eW
    F.N.equiv F.ExpN F.isExpN haarN dynkinN b₀
  refine ⟨D, hD, ?_⟩
  filter_upwards [hslack, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  obtain ⟨hcontain, hvolume⟩ := hdenom E β hβ r hr0
  refine ⟨?_, hvolume _⟩
  intro j x hx u hu
  obtain ⟨t, ht, rfl⟩ := hu
  have ht' : |t| ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using ht
  apply hcontain _ _ ?_ x hx
  simpa only [rootIntervalSample_letter, smul_smul, Function.comp_apply] using hr (letters j) t ht'

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootIntervalPadding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unused interval indices contribute only the group identity -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {L N I : Type} [AddCommGroup L] [Module ℝ L] [Group N]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

omit [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N] in
/-- Padding the fixed endpoint word does not enlarge any recurrence cell. -/
theorem rootIntervalSupport_of_le (Exp : L → N) (hzero : Exp 0 = 1)
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r R : ℝ) (j : ℕ) (hj : m ≤ j) (hR : 0 ≤ R) :
    rootIntervalSupport Exp letters X s r R j = {1} := by
  ext u
  constructor
  · rintro ⟨t, _, rfl⟩
    simp [rootIntervalSample, rootIntervalDirection, Nat.not_lt.mpr hj, hzero]
  · rintro rfl
    refine ⟨0, ?_, ?_⟩
    · simpa using hR
    · simp [rootIntervalSample, rootIntervalDirection, Nat.not_lt.mpr hj, hzero]

omit [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N] in
/-- A finite collection of denominator bounds covers the padded family. -/
theorem rootIntervalSupport_mul_mem_padded (Exp : L → N) (hzero : Exp 0 = 1)
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r R : ℝ) (hR : 0 ≤ R) {Q Q' : Set N} (hQQ : Q ⊆ Q')
    (hfinite : ∀ j : Fin m, ∀ x ∈ Q,
      ∀ u ∈ rootIntervalSupport Exp letters X s r R j.val, x * u ∈ Q') :
    ∀ j : ℕ, ∀ x ∈ Q, ∀ u ∈ rootIntervalSupport Exp letters X s r R j, x * u ∈ Q' := by
  intro j x hx u hu
  by_cases hj : j < m
  · exact hfinite ⟨j, hj⟩ x hx u hu
  · rw [rootIntervalSupport_of_le Exp hzero letters X s r R j (Nat.le_of_not_gt hj) hR] at hu
    have he : u = 1 := mem_singleton_iff.mp hu
    simpa only [he, mul_one] using hQQ hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SequenceCartanDenominator
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The compact support of every original interval law fits into one fixed
translated enlarged box. Its exact Haar-volume ratio is independent of scale. -/
theorem exists_interval_recurrence_denominator_sequence
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    {m : ℕ} (letters : Fin m → Fin M.letterCount) :
    ∃ D : ℝ, 1 ≤ D ∧
      let μ := MeasureTheory.Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm)
        MeasureTheory.volume
      ∀ᶠ r in atTop,
        let k₀ := F.ExpN (F.N.equiv (k r))
        let Q := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale r) 1
        let Q' := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale r) D
        (∀ j : Fin m, ∀ x ∈ Q,
          ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q (scale r) R j.val,
            x * u ∈ Q') ∧
        μ Q' = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ Q := by
  let ε' := extendOnScales scale ε 0
  let k' := extendOnScales scale k 0
  have hε' : Tendsto ε' atTop (𝓝 0) := tendsto_extendOnScales hmono hε
  have hε'pos (t : ℝ) : 0 ≤ ε' t := by
    dsimp [ε', extendOnScales]
    split_ifs
    · exact hεpos _
    · exact le_rfl
  have hk' : ∀ᶠ t : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun (k' t)‖ ≤
          Real.exp (t * ε' t) := by
    apply eventually_extendOnScales hmono k 0
      (fun t y => ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun y‖ ≤
          Real.exp (t * ε' t))
    · intro t
      simp only [map_zero, norm_zero]
      exact (Real.exp_pos _).le
    · simpa only [ε', extendOnScales_apply hmono] using hk
  obtain ⟨D, hD, hbound⟩ := M.exists_interval_recurrence_denominator T F hunimod eW
    hExpG realize haarN dynkinN b₀ E β q hβ hδ hc hhi hR hcost hgap hq
    ε' hε'pos hε' k' hk' letters
  refine ⟨D, hD, ?_⟩
  simpa only [k', extendOnScales_apply hmono] using hscale.eventually hbound

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanRecurrenceCells
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter MeasureTheory Set
open scoped Manifold Topology Matrix.Norms.Operator ENNReal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The compact support of every original interval law fits into one fixed
translated enlarged box. Its exact Haar-volume ratio is independent of scale. -/
theorem exists_interval_recurrence_cells_sequence
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    {m : ℕ} (letters : Fin m → Fin M.letterCount) :
    ∃ D : ℝ, 1 ≤ D ∧
      let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
      let B := fun n R => (fun y => y * F.ExpN (F.N.equiv (k n))) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) R
      (∀ n, 0 < (μ (B n 1)).toReal ∧ μ (B n 1) ≠ ∞ ∧
        0 < (μ (B n D)).toReal ∧ μ (B n D) ≠ ∞) ∧
      (∀ n, (μ (B n D)).toReal = D ^ finrank ℝ (cartanRootIdeal H) * (μ (B n 1)).toReal) ∧
      ∀ᶠ n in atTop, ∀ j : ℕ, ∀ x ∈ B n 1,
        ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q (scale n) R j,
          x * u ∈ B n D := by
  obtain ⟨D, hD, hbound⟩ := M.exists_interval_recurrence_denominator_sequence
    T F hunimod eW hExpG realize haarN dynkinN b₀ E β q hβ hδ hc hhi hR hcost hgap hq
    scale hscale hmono ε hεpos hε k hk letters
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let B := fun n R => (fun y => y * F.ExpN (F.N.equiv (k n))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) R
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv hnil F.ExpN F.isExpN b₀
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN (F.N.tangent_nilpotent hnil)
  have hmass (n : ℕ) (R' : ℝ) (hR' : 0 < R') :
      0 < (μ (B n R')).toReal ∧ μ (B n R') ≠ ∞ := by
    have hh := translated_exponential_cell_mass haarN F.N.equiv hnil F.ExpN F.isExpN
      chartN hchartN M.letter M.wordList b₀ β (M.boxCost T hunimod eW E) (scale n)
      (F.ExpN (F.N.equiv (k n))) (Icc (fun _ => -R') (fun _ => R'))
      (coordinate_cube_mass hR').1 (coordinate_cube_mass hR').2
    dsimp only [B, groupBox]
    rw [exponentialCoordinateBox_eq_cube_image _ _ R' hR'.le, ← image_comp]
    exact hh
  refine ⟨D, hD, ?_⟩
  change (∀ n, _) ∧ (∀ n, _) ∧ _
  refine ⟨fun n => ⟨(hmass n 1 zero_lt_one).1, (hmass n 1 zero_lt_one).2,
    (hmass n D (zero_lt_one.trans_le hD)).1, (hmass n D (zero_lt_one.trans_le hD)).2⟩, ?_, ?_⟩
  · intro n
    have he : μ (B n D) = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ (B n 1) := by
      dsimp only [B]
      rw [measure_image_mul_right μ, measure_image_mul_right μ]
      exact exponential_box_radius_measure F.N.equiv F.ExpN chartN hchartN b₀
        (M.boxBasis T hunimod eW E β (scale n)) (zero_le_one.trans hD)
    rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (zero_le_one.trans hD) _)]
  · filter_upwards [hbound] with n hn
    apply rootIntervalSupport_mul_mem_padded (F.ExpN ∘ F.N.equiv)
      (by simp [F.isExpN.map_zero]) letters M.letter q (scale n) R hR ?_ hn.1
    apply image_mono
    rintro x ⟨v, hv, hnorm⟩
    exact ⟨v, hv, hnorm.trans hD⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WordChartFlowHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact height of a word-chart horizontal flow and its graded limit -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter Set
open scoped Topology

variable {L G W I : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]

omit [FiniteDimensional ℝ L] in
/-- Exact height is retained at every finite physical scale. -/
theorem wordChartFlow_height (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (h : L →ₗ[ℝ] W)
    (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {r : ℝ} (hr : 1 ≤ r) (v : L) (z : Fin (finrank ℝ L) → ℝ) (t : ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (max (Real.log r) 0)
    h (b.equivFun.symm (dynkinFlowMap a (basisBracket br) (br.equivFun (r • v)) (z, t))) =
      h (b.equivFun.symm z) + t • h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := exponentialRescaleBasis b cost (max (Real.log r) 0)
  let flow := dynkinFlowMap a (basisBracket br) (br.equivFun (r • v))
  have he := congrArg (fun g : G => (π g).toAdd) (exp_basis_horizontal_flow Exp br a hm r t v z)
  simp only [hπ, map_mul, toAdd_mul, map_smul] at he
  have hp (w : Fin (finrank ℝ L) → ℝ) : h (br.equivFun.symm w) = r • h (b.equivFun.symm w) :=
    wordChartPivot_height X S β h hh hr w
  rw [hp, hp] at he
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have he' := congrArg (fun w : W => r⁻¹ • w) he
  simpa only [b, cost, br, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hr0, one_smul,
    ← mul_assoc, inv_mul_cancel₀ hr0, one_mul] using he'

omit [FiniteDimensional ℝ L] in
/-- The limiting horizontal flow projects to the original affine segment.
This follows from convergence and the finite-scale identity, without an
extra homomorphism premise on the limiting polynomial group. -/
theorem gradedWordChartFlow_height (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (h : L →ₗ[ℝ] W)
    (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (z : Fin (finrank ℝ L) → ℝ) (t : ℝ)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
          ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
        bracketWordExponent (fun _ : I => 1) (β.val i) +
            bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k)) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm
      (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) =
        h (b.equivFun.symm z) + t • h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let p := h.comp b.equivFun.symm.toLinearMap
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  have hf := rescaled_horizontal_flow_tendstoUniformlyOn a b cost hweight v hv
    (isCompact_singleton (x := (z, t)))
  have heval := hf.tendsto_at (mem_singleton (z, t))
  have hp := p.continuous_of_finiteDimensional.tendsto _ |>.comp heval
  have hconst : ∀ᶠ s : ℝ in atTop,
      p (dynkinProduct a (basisBracket (exponentialRescaleBasis b cost s)) z
        (t • (exponentialRescaleBasis b cost s).equivFun (Real.exp s • v))) =
        h (b.equivFun.symm z) + t • h v := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    change h (b.equivFun.symm (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost s)) z
      (t • (exponentialRescaleBasis b cost s).equivFun (Real.exp s • v)))) = _
    have he := wordChartFlow_height X S β h hh Exp π hπ a hm
      (Real.one_le_exp_iff.mpr hs) v z t
    simpa only [p, b, cost, LinearMap.comp_apply, dynkinFlowMap, ContinuousMap.coe_mk,
      Real.log_exp, max_eq_left hs] using he
  exact tendsto_nhds_unique hp (tendsto_const_nhds.congr' (hconst.mono fun _ he => he.symm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FlowSegmentImages
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact height images of the graded horizontal segments -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

theorem isCompact_segment_real {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (x y : W) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

theorem SupportDatum.templateSupport_affine_segment
    {W I B : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] (P : SupportDatum W I B)
    (w v : W) {T : ℝ} (hT : 0 ≤ T) :
    P.templateSupport (segment ℝ w (w + T • v)) = T * P.segmentSupport v := by
  have he : segment ℝ w (w + T • v) = (fun y => y + w) '' segment ℝ 0 (T • v) := by
    simpa only [add_zero, zero_add, add_comm] using
      (segment_translate_image ℝ w (0 : W) (T • v)).symm
  rw [he, P.templateSupport_translate (isCompact_segment_real _ _) ⟨_, left_mem_segment ℝ _ _⟩,
    P.templateSupport_segment, P.segmentSupport_smul_of_nonneg _ hT]

theorem affine_interval_image {W : Type} [AddCommGroup W] [Module ℝ W]
    (w v : W) {T : ℝ} (hT : 0 < T) :
    (fun t : ℝ => w + t • v) '' Icc 0 T = segment ℝ w (w + T • v) := by
  rw [segment_eq_image']
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / T, ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hT.ne']
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * T, ⟨mul_nonneg ht.1 hT.le, ?_⟩, ?_⟩
    · simpa using mul_le_mul_of_nonneg_right ht.2 hT.le
    · simp only [add_sub_cancel_left, smul_smul]

/-- The entire limiting horizontal segment has exactly its expected
affine height image, including both endpoints. -/
theorem gradedWordChartFlow_height_image
    {L G W I : Type} [LieRing L] [LieAlgebra ℝ L]
    [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (z : Fin (finrank ℝ L) → ℝ) {T : ℝ} (hT : 0 < T)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
          ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
        bracketWordExponent (fun _ : I => 1) (β.val i) +
            bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k)) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let F := dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
    (fun y => h (b.equivFun.symm y)) '' ((fun t => F (z, t)) '' Icc 0 T) =
      segment ℝ (h (b.equivFun.symm z)) (h (b.equivFun.symm z) + T • h v) := by
  dsimp only
  rw [← image_comp]
  convert affine_interval_image (h ((WordBasisSelections.basis X S β).equivFun.symm z)) (h v) hT using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext t
  exact gradedWordChartFlow_height X S β h hh Exp π hπ a hm v z t hweight

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProfileSegmentVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.gradedGeneratorMap_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The volume inequality for supported limiting Cartan chart profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal ENNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0}

set_option maxHeartbeats 1000000 in
/-- The fixed submersive word is selected before good profiles are retained.
Actual interval laws and a fixed enlarged Haar box then supply recurrence,
and the physical segment legs yield the support-volume inequality. -/
theorem cartan_profile_segment_volume_sequence_oai
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
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
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y, y ∈ Icc
      (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) →
      ∀ z, (profile n y).val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (f := (profile n)) (by first | exact (hp n).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν)) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let P := M.supportIn T hunimod eW
    ∀ (v : H) (z : Fin (finrank ℝ H) → ℝ) (T₀ : ℝ), 0 < T₀ →
      let flow := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
      ∀ (U : Set (Fin (finrank ℝ H) → ℝ)), IsOpen U →
        (∀ y ∈ U, eW (heightProjection T.character (b.equivFun.symm y :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E) →
        (∀ t ∈ Icc 0 T₀, flow (z, t) ∈ U) →
        ∀ f : S, f ∈ (ν : Measure S).support →
          T₀ * P.segmentSupport (eW (heightProjection T.character v)) ≤
            P.templateSupport ((fun t => f.val (flow (z, t))) '' Icc 0 T₀) := by
  dsimp only
  intro v z T₀ hT₀ U hU hUheight hseg f hf
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let flow := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  let P := M.supportIn T hunimod eW
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap)
  let source := segment ℝ (h (b.equivFun.symm z)) (h (b.equivFun.symm z) + T₀ • h v)
  have hbr (u v : H) : h ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), v⁆) = 0
    rw [T.height_lie, map_zero]
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  have hExpHeight (u : H) :
      ((π.comp F.inclusionD) ((F.ExpD ∘ F.D.equiv) u)).toAdd = h u := by
    simp only [MonoidHom.comp_apply, Function.comp_apply, F.compatibleD, hπExp]
    rfl
  have himage := gradedWordChartFlow_height_image X (boundedBracketWords d) βD h hbr
    (F.ExpD ∘ F.D.equiv) (π.comp F.inclusionD) hExpHeight aD
    (model_binary_dynkin F.D.equiv F.ExpD aD hmD) v z hT₀ hweight
  change (fun y => h (b.equivFun.symm y)) '' ((fun t => flow (z, t)) '' Icc 0 T₀) = source at himage
  have hsourceSub : source ⊆ (fun w => (1 - c * δ) • w) '' E := by
    rw [← himage]
    rintro w ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact hUheight _ (hseg t ht)
  have hq (i : Fin M.letterCount) :
      P.weightSupport source i ≤ (1 - c * δ) * P.weightSupport E i := by
    have hh := P.weightSupport_mono (isCompact_segment_real _ _) ⟨_, left_mem_segment ℝ _ _⟩
      (hE.image (continuous_const.smul continuous_id)) hsourceSub i
    change P.weightSupport source i ≤ P.weightSupport ((fun w : W => (1 - c * δ) • w) '' E) i at hh
    exact hh.trans_eq (P.weightSupport_image_smul hE hne ht i)
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ source
  obtain ⟨C₀, hC₀, hparams⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b₀ aN hmN source γ hγ
  let parameters := normalizedExponentialParameters aN
    (fun i => (γ.val i : FreeMagma (Fin M.letterCount))) (fun i => Pi.single i (1 : ℝ)) C₀
  let law := fun n => rescaledLieData M.letter M.wordList γ (P.weightSupport source) (scale n)
  have hlaw (n : ℕ) : law n ∈ parameters := hparams (scale n) (zero_le_one.trans (hscale1 n))
  obtain ⟨q, hqmem, u, hu, hlim, m, letters, t₀, _, honto⟩ :=
    exists_submersive_scheme_of_normalized_sequence aN
      (fun i => (γ.val i : FreeMagma (Fin M.letterCount))) C₀ law hlaw
  let ρ := max 1 ‖t₀‖
  have hρ : 1 ≤ ρ := le_max_left _ _
  have ht₀ : ‖t₀‖ ≤ ρ := le_max_right _ _
  have hru : Tendsto (scale ∘ u) atTop atTop := hscale.comp hu.tendsto_atTop
  have hku := hu.tendsto_atTop.eventually hk
  have hcells := M.exists_interval_recurrence_cells_sequence T F hunimod eW hExp realize
    haarN dynkinN b₀ E β (P.weightSupport source) hβ hδ hc hhi (zero_le_one.trans hρ)
    hcost hgap hq (scale ∘ u) hru (hmono.comp hu) (ε ∘ u)
    (fun n => hεpos (u n)) (hε.comp hu.tendsto_atTop) (k ∘ u) hku letters
  dsimp only at hcells
  rcases hcells with ⟨D₀, hD₀, hmass, hratio, hcontain⟩
  obtain ⟨w, hw, hwgood⟩ := extraction_of_eventually_atTop hcontain
  let index := u ∘ w
  have hindex := hu.comp hw
  have hr : Tendsto (scale ∘ index) atTop atTop := hscale.comp hindex.tendsto_atTop
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  have hcube := coordinate_cube_mass (n := finrank ℝ (cartanRootIdeal H)) zero_lt_one
  have hg : Continuous (fun t => f.val (flow (z, t))) :=
    f.val.continuous.comp (flow.continuous.comp (continuous_const.prodMk continuous_id))
  have hgood := M.exists_good_cartan_cell_legs_sequence T F hunimod eW haarN chartN hchartN
    b₀ E β (scale ∘ index) hr (k ∘ index) X hDnil bD₀ βD hβD aD hmD
    (fun n g => (π ((p (index n)).val.1 g)).toAdd) (x ∘ index)
    cube measurableSet_Icc hcube.1 hcube.2 S (fun n => profile (index n))
    (fun n => hp (index n)) ν (hν.comp hindex.tendsto_atTop)
    v z T₀ U hU hseg (fun n y hy z => hactual (index n) y hy z) hf
  dsimp only at hgood
  rcases hgood with ⟨A, ζ, hA, hAQ, hApos, hζpos, hζ, hAlower, hlegs⟩
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let Q := fun n => (fun y => y * F.ExpN (F.N.equiv (k (index n)))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) 1
  let R := fun n => (fun y => y * F.ExpN (F.N.equiv (k (index n)))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) D₀
  have hQ (n : ℕ) : Q n =
      (fun y => F.ExpN (F.N.equiv ((M.boxBasis T hunimod eW E β (scale (index n))).equivFun.symm y)) *
        F.ExpN (F.N.equiv (k (index n)))) '' cube := by
    dsimp only [Q, groupBox]
    rw [exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  let sample := fun n j t => rootIntervalSample (F.ExpN ∘ F.N.equiv) letters M.letter
    (P.weightSupport source) (scale (index n)) j t
  let σ := fun n j => rootIntervalLaw (F.ExpN ∘ F.N.equiv) letters M.letter
    (P.weightSupport source) (scale (index n)) ρ j
  have hcont (v : cartanRootIdeal H) : Continuous (fun t : ℝ => (F.ExpN ∘ F.N.equiv) (t • v)) := by
    have hb := continuous_model_exp_coordinates haarN F.ExpN F.isExpN F.N.equiv
      (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) b₀
    have he (t : ℝ) : (F.ExpN ∘ F.N.equiv) (t • v) =
        F.ExpN (F.N.equiv (b₀.equivFun.symm (t • b₀.equivFun v))) := by simp
    simp_rw [he]
    exact hb.comp (continuous_id.smul continuous_const)
  let : ∀ n j, IsProbabilityMeasure (σ n j) := fun n j =>
    rootIntervalLaw_isProbability _ hcont letters M.letter _ _ (zero_lt_one.trans_le hρ) j
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  have hpack := M.templateSupport_le_of_recurrent_segment_cells_sequence_m T F hunimod eW π hπExp
    dynkinN dynkinD haarN haarD hExp realize (scale ∘ index) hr
    (fun n => hscale1 (index n)) b₀ X (boundedBracketWords d) βD z v hT₀ source rfl γ hγ
    (x ∘ index) A Q (fun n j => rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter
      (P.weightSupport source) (scale (index n)) ρ j) (fun n _ => R n) (fun _ _ => D₀ ^ finrank ℝ (cartanRootIdeal H))
    μ (p ∘ index) hΛ hpath hπ aN hmN letters sample
    (fun n j t s => rootIntervalSample_sub _
      (fun v => by simp [F.isExpN.map_neg])
      (fun v t s => by simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) t s)
      letters M.letter _ _ j t s)
    (fun n j t => rootIntervalSample_letter _ letters M.letter _ _ j t)
    parameters (isCompact_normalizedExponentialParameters _ _ _ _)
    (fun n => hlaw (index n)) q hqmem (hlim.comp hw.tendsto_atTop)
    rem hdim ρ hρ t₀ ht₀ honto σ
    (fun n j => measurePreserving_rootIntervalSample _ hcont letters M.letter _ _ _ j)
    (fun n => (hmass (w n)).2.1) (fun n => (hmass (w n)).1)
    (fun n j => rootIntervalLaw_ae_mem_support _ hcont letters M.letter _ _ _ j)
    (fun n j => (hmass (w n)).2.2.2) (fun n j => (hmass (w n)).2.2.1)
    (fun n j => hwgood n j) (fun n j => pow_pos (zero_lt_one.trans_le hD₀) _)
    (fun n j => le_of_eq (hratio (w n))) hA
    (fun n => by simpa only [hQ n, Function.comp_apply] using hAQ n) hApos
    (by simpa only [hQ, Function.comp_apply, μ] using hAlower)
    (fun j _ => sequence_subexponential_upper_const hr _) (fun t => f.val (flow (z, t))) hg
    (fun n => (π ((p (index n)).val.1 (x (index n)))).toAdd) ζ hζ hlegs
  have hsourceExp : P.templateSupport source = T₀ * P.segmentSupport (h v) :=
    P.templateSupport_affine_segment _ _ hT₀.le
  rw [hsourceExp] at hpack
  exact hpack

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence_oai := @OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence_oai
