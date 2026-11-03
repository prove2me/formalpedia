-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:08:42.741406+00:00
-- url     : https://prove2.me/submissions/5ce776f3-8ebc-4e1e-aabe-c482253a881b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_coarse_path_polynomial_packing
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_segmentWordPath_bound

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

/-- The word length is fixed even though the inserted amplitudes vary. -/
theorem length_generatorSchemeWord {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (generatorSchemeWord w i t).length = ∑ k, (2 * (w k).length + 1) := by
  simp [generatorSchemeWord, inverseGeneratorWord, List.length_flatten,
    List.map_ofFn, List.sum_ofFn]
  congr 1
  funext k
  omega

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedGeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative bounds for a fixed generator scheme

The fixed conjugating words give a common amplitude bound; scaling a
logarithm into the local product chart and repeating the resulting word
covers any prescribed bounded logarithmic set.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I : Type}

/-- Amplitudes in every fixed conjugating word admit one finite bound. -/
theorem exists_fixed_word_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k, ∀ p ∈ w k, |p.2| ≤ C := by
  let S := (List.ofFn w).flatten
  let C := 1 + (S.map (fun p => |p.2|)).sum
  have hnonneg : ∀ x ∈ S.map (fun p => |p.2|), (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  refine ⟨C, by dsimp [C] <;> linarith [List.sum_nonneg hnonneg], ?_⟩
  intro k p hp
  have hpS : p ∈ S := by
    exact List.mem_flatten.mpr ⟨w k, List.mem_ofFn.mpr ⟨k, rfl⟩, hp⟩
  have h := List.single_le_sum hnonneg |p.2| (List.mem_map.mpr ⟨p, hpS, rfl⟩)
  dsimp [C]
  linarith

/-- Inserting unit-bounded parameters keeps every amplitude uniformly bounded. -/
theorem generatorSchemeWord_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ))
    (i : Fin n → I) {C : ℝ} (hC : 1 ≤ C)
    (hw : ∀ k, ∀ p ∈ w k, |p.2| ≤ C) (t : Fin n → ℝ) (ht : ‖t‖ ≤ 1) :
    ∀ p ∈ generatorSchemeWord w i t, |p.2| ≤ C := by
  intro p hp
  obtain ⟨s, hs, hp⟩ := List.mem_flatten.mp hp
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hs
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hw k p hp
    · have he : p = (i k, t k) := by simpa using hp
      rw [he]
      exact ((Real.norm_eq_abs _ ▸ norm_le_pi_norm t k).trans ht).trans hC
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq' : q ∈ w k := List.mem_reverse.mp hq
    simpa only [abs_neg] using hw k q hq'

end PolycyclicRecognition

end

end OAI
end

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

set_option maxHeartbeats 1000000 in
/-- Every maximizing basis has the same template exponent, including ties. -/
theorem columnBasisWeight_eq_templateSupport_of_maximizing
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod e E) β.val) :
    columnBasisWeight (M.boxCost T hunimod e E) β.val =
      (M.supportIn T hunimod e).templateSupport E := by
  obtain ⟨γ, _, hγ⟩ := M.exists_maximizing_box_basis T hunimod e b₀ E
  apply le_antisymm
  · rw [M.columnBasisWeight_boxCost]
    exact (M.supportIn T hunimod e).basisTemplateSupport_le E β
  · rw [← hγ]
    exact hβ.2 γ.val (wordBasis_det_ne_zero M.letter M.wordList b₀ γ)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParametricSubmersion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local images for nearby parameters

Apply the ordinary submersion theorem to the joint map `(p,x) ↦ (p,f(p,x))`.
A surjective derivative in the second variable then gives a common image
neighborhood for all nearby parameters. This is the persistence step for
normalized generator product schemes.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Metric
open scoped Topology

variable {P E F : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace P] [CompleteSpace E] [CompleteSpace F] in
/-- Surjectivity in the second variable makes the parameter-preserving
joint differential surjective. -/
theorem parameter_joint_derivative_surjective (D : (P × E) →L[ℝ] F)
    (hD : Function.Surjective (fun v : E => D (0, v))) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ P E).prod D) := by
  rintro ⟨p, y⟩
  obtain ⟨v, hv⟩ := hD (y - D (p, 0))
  change D (0, v) = y - D (p, 0) at hv
  refine ⟨(p, v), ?_⟩
  change (p, D (p, v)) = (p, y)
  refine Prod.ext (by rfl) ?_
  change D (p, v) = y
  have he : (p, v) = (p, 0) + (0, v) := by simp
  rw [he, map_add, hv, add_sub_cancel]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactSubmersionFamily
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite collection of uniform local charts

Compactness reduces a family with pointwise nondegenerate endpoint schemes
to finitely many schemes covering one common target neighborhood.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem finite_positive_lower_bound {I : Type} (s : Finset I)
    (r : I → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ε, hε, hb⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min (r i) ε, lt_min (hr i (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParametricInverseSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous local inverse sections with parameters

For the square amplitude map in a generator scheme, the parameter-preserving
inverse function theorem supplies a continuous choice of amplitudes, jointly
with the normalized group law. Its source bound is retained explicitly for
the subsequent measurable endpoint sampling.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Metric
open scoped Topology

variable {P E F : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace P] [CompleteSpace E] [CompleteSpace F] in
theorem parameter_joint_derivative_bijective (D : (P × E) →L[ℝ] F)
    (hD : Function.Bijective (fun v : E => D (0, v))) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ P E).prod D) := by
  refine ⟨?_, parameter_joint_derivative_surjective D hD.2⟩
  rintro ⟨p, v⟩ ⟨q, w⟩ he
  have hp : p = q := congrArg Prod.fst he
  subst q
  have hs : D (p, v) = D (p, w) := congrArg Prod.snd he
  have hv : D (0, v) = D (0, w) := by
    have ha (t : E) : D (p, t) = D (p, 0) + D (0, t) := by
      rw [← map_add]
      congr 1
      simp
    rw [ha v, ha w] at hs
    exact add_left_cancel hs
  exact Prod.ext rfl (hD.1 hv)

/-- Nearby parameters admit a common target ball and continuous local
amplitude choices of the prescribed bounded size. -/
theorem exists_parametric_inverse_section (f : P × E → F) (p : P)
    (hf : ContDiffAt ℝ 1 f (p, 0)) (hz : f (p, 0) = 0)
    (hbij : Function.Bijective (fun v : E => fderiv ℝ f (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ s : P × F → E, ContinuousOn s (U ×ˢ ball 0 ε) ∧
        ∀ q ∈ U, ∀ y ∈ ball (0 : F) ε, f (q, s (q, y)) = y ∧ ‖s (q, y)‖ < R := by
  let H : P × E → P × F := fun z => (z.1, f z)
  let D := (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ f (p, 0))
  have hD : Function.Bijective D := parameter_joint_derivative_bijective _ hbij
  let eD : (P × E) ≃L[ℝ] (P × F) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hderiv : HasStrictFDerivAt H (eD : (P × E) →L[ℝ] (P × F)) (p, 0) := by
    change HasStrictFDerivAt H D (p, 0)
    exact (hasStrictFDerivAt_fst (p := (p, (0 : E)))).prodMk
      (hf.hasStrictFDerivAt one_ne_zero)
  let e := hderiv.toOpenPartialHomeomorph H
  have hsource : (p, (0 : E)) ∈ e.source := hderiv.mem_toOpenPartialHomeomorph_source
  have hvalue : H (p, 0) = (p, (0 : F)) := by simp [H, hz]
  have htarget : (p, (0 : F)) ∈ e.target := by
    simpa only [hvalue] using hderiv.image_mem_toOpenPartialHomeomorph_target
  have hinv : e.symm (p, 0) = (p, (0 : E)) := by
    rw [← hvalue]
    exact e.left_inv hsource
  have hcont : ContinuousAt e.symm (p, (0 : F)) := e.continuousAt_symm htarget
  have hsmall : e.symm ⁻¹' ((univ : Set P) ×ˢ ball (0 : E) R) ∈ 𝓝 (p, (0 : F)) := by
    apply hcont.preimage_mem_nhds
    rw [hinv]
    exact prod_mem_nhds Filter.univ_mem (ball_mem_nhds _ hR)
  have hN := inter_mem (e.open_target.mem_nhds htarget) hsmall
  obtain ⟨U, V, hU, hp, hV, h0, hUV⟩ := mem_nhds_prod_iff'.mp hN
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let s : P × F → E := fun z => (e.symm z).2
  have hsub : U ×ˢ ball (0 : F) ε ⊆ e.target := fun z hz =>
    (hUV ⟨hz.1, hεV hz.2⟩).1
  refine ⟨U, hU, hp, ε, hε, s,
    continuous_snd.comp_continuousOn (e.symm.continuousOn.mono hsub), ?_⟩
  intro q hq y hy
  have ht := hsub (show (q, y) ∈ U ×ˢ ball (0 : F) ε from ⟨hq, hy⟩)
  have he := e.right_inv ht
  have hp' : (e.symm (q, y)).1 = q := congrArg Prod.fst he
  have hf' : f (e.symm (q, y)) = y := congrArg Prod.snd he
  have hpair : e.symm (q, y) = (q, s (q, y)) := Prod.ext hp' rfl
  refine ⟨?_, ?_⟩
  · rw [hpair] at hf'
    exact hf'
  · have hm := (hUV (show (q, y) ∈ U ×ˢ V from ⟨hq, hεV hy⟩)).2
    exact mem_ball_zero_iff.mp hm.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactInverseSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite continuous inverse sections on a compact parameter family

The common image ball is retained together with continuous amplitude
choices, rather than just existential preimages. This is the form needed
to sample endpoints measurably in a stationary volume argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {P E F J : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Finitely many actual schemes admit bounded continuous inverse sections
on one common ball, uniformly over the compact parameter set. -/
theorem exists_finite_uniform_inverse_sections
    (f : J → P × E → F) {K : Set P} (hK : IsCompact K)
    (h : ∀ p ∈ K, ∃ j, ContDiffAt ℝ 1 (f j) (p, 0) ∧ f j (p, 0) = 0 ∧
      Function.Bijective (fun v : E => fderiv ℝ (f j) (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ (S : Finset J) (ε : ℝ), 0 < ε ∧ ∀ p ∈ K, ∃ j ∈ S,
      ∃ s : F → E, ContinuousOn s (ball 0 ε) ∧
        ∀ y ∈ ball (0 : F) ε, f j (p, s y) = y ∧ ‖s y‖ < R := by
  classical
  choose j hc hz hb using (fun p : K => h p.val p.property)
  choose U hU hp r hr s hs hsection using (fun p : K =>
    exists_parametric_inverse_section (f (j p)) p.val (hc p) (hz p) (hb p) hR)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hU (by
    intro p hpK
    exact mem_iUnion.mpr ⟨⟨p, hpK⟩, hp ⟨p, hpK⟩⟩)
  obtain ⟨ε, hε, hεr⟩ := finite_positive_lower_bound S r (fun p _ => hr p)
  refine ⟨S.image j, ε, hε, ?_⟩
  intro p hpK
  obtain ⟨q, hq, hpU⟩ := mem_iUnion₂.mp (hS hpK)
  refine ⟨j q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, fun y => s q (p, y), ?_, ?_⟩
  · apply (hs q).comp (continuous_const.prodMk continuous_id).continuousOn
    intro y hy
    exact ⟨hpU, ball_subset_ball (hεr q hq) hy⟩
  · intro y hy
    exact hsection q p hpU y (ball_subset_ball (hεr q hq) hy)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateInverseSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous inverses for the normalized generator schemes

The amplitude differential is square. Its already proved surjectivity is
therefore bijectivity, so compactness supplies a finite set of schemes with
continuous inverse sections on one common coordinate ball.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric

variable {I V : Type} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Measurable endpoint coding for every actual normalized law: the inverse
is continuous on the common ball, and all its amplitudes are bounded by one. -/
theorem exists_uniform_coordinate_inverse_sections {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I) (C : ℝ) :
    ∃ (schemes : Finset ((Fin (finrank ℝ V) → List (I × ℝ)) ×
        (Fin (finrank ℝ V) → I))) (ε : ℝ), 0 < ε ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C,
        ∃ s ∈ schemes, ∃ σ : V → (Fin (finrank ℝ V) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : V) ε,
            polynomialEndpointScheme a s.1 s.2 p (σ y) = y ∧ ‖σ y‖ < 1 := by
  let f := fun s : (Fin (finrank ℝ V) → List (I × ℝ)) × (Fin (finrank ℝ V) → I) =>
    fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin (finrank ℝ V) → ℝ) =>
      polynomialEndpointScheme a s.1 s.2 z.1 z.2
  apply exists_finite_uniform_inverse_sections f
    (isCompact_normalizedExponentialParameters a w₀ b₀ C) _ zero_lt_one
  intro p hp
  rcases hp with ⟨⟨⟨_, _, hB, hw⟩, hg⟩, hc⟩
  obtain ⟨w, i, hz, hs⟩ := exists_coordinate_submersive_scheme a p.1 hB hg hc p.2 b₀ w₀ hw
  refine ⟨(w, i), (contDiff_polynomialEndpointScheme (V := V) (k := 1) a w i).contDiffAt,
    hz, ?_⟩
  let D : (Fin (finrank ℝ V) → ℝ) →L[ℝ] V :=
    (fderiv ℝ (f (w, i)) (p, 0)).comp
      (ContinuousLinearMap.inr ℝ ((V →L[ℝ] V →L[ℝ] V) × (I → V)) _)
  have hsurj : Function.Surjective D := hs
  have hinj : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := D.toLinearMap) (by simp)).mpr hsurj
  exact ⟨hinj, hs⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateBoundedInverse
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the continuous inverse schemes

The finite cover by inverse sections provides common bounds on expanded
word length and on every amplitude, without a measurable-choice premise.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Metric
open scoped BigOperators

variable {I V : Type} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [Fintype I] in
/-- The direct word and the expanded endpoint polynomial agree for an
actual polynomial coordinate group. -/
theorem polynomialWord_generatorScheme_eq {c n : ℕ}
    (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (hg : PolynomialGroupLaws (dynkinProduct a B)) (X : I → V)
    (w : Fin n → List (I × ℝ)) (i : Fin n → I) (t : Fin n → ℝ) :
    polynomialWord (dynkinProduct a B) X (generatorSchemeWord w i t) =
      polynomialEndpointScheme a w i (B, X) t :=
  (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg).injective
    ((exp_polynomialWord _ hg X _).trans
      (exp_polynomialEndpointScheme a B hB hg X w i t).symm)

/-- Every normalized law has one continuous bounded inverse scheme on a
common ball; its expanded words have common length and amplitude bounds. -/
theorem exists_uniform_bounded_coordinate_inverse {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I) (C₀ : ℝ) (n : ℕ) (hdim : finrank ℝ V = n) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C₀,
        ∃ (w : Fin n → List (I × ℝ)) (i : Fin n → I)
          (σ : V → Fin n → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : V) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            polynomialWord (dynkinProduct a p.1) p.2 (generatorSchemeWord w i (σ y)) = y := by
  subst n
  classical
  obtain ⟨schemes, ε, hε, hcover⟩ := exists_uniform_coordinate_inverse_sections a b₀ w₀ C₀
  let A (s : (Fin (finrank ℝ V) → List (I × ℝ)) × (Fin (finrank ℝ V) → I)) :=
    Classical.choose (exists_fixed_word_amplitude_bound s.1)
  have hA s : 1 ≤ A s ∧ ∀ j, ∀ z ∈ s.1 j, |z.2| ≤ A s :=
    Classical.choose_spec (exists_fixed_word_amplitude_bound s.1)
  let C := 1 + ∑ s ∈ schemes, A s
  have hAnonneg s : 0 ≤ A s := (by norm_num : (0 : ℝ) ≤ 1).trans (hA s).1
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun s _ => hAnonneg s))
  have hAC s (hs : s ∈ schemes) : A s ≤ C := by
    have hh := Finset.single_le_sum (fun t _ => hAnonneg t) hs
    dsimp [C]
    linarith
  let N := ∑ s ∈ schemes, ∑ j, (2 * (s.1 j).length + 1)
  refine ⟨ε, N, C, hε, hC, ?_⟩
  intro p hp
  obtain ⟨s, hs, σ, hσ, hright⟩ := hcover p hp
  have hBracket := hp.1.1.2.2.1
  have hGroup := hp.1.2
  refine ⟨s.1, s.2, σ, hσ, ?_⟩
  intro y hy
  obtain ⟨he, hnorm⟩ := hright y hy
  refine ⟨hnorm, ?_, ?_, ?_⟩
  · rw [length_generatorSchemeWord]
    exact Finset.single_le_sum
      (f := fun q => ∑ j, (2 * (q.1 j).length + 1)) (fun _ _ => Nat.zero_le _) hs
  · intro z hz
    exact (generatorSchemeWord_amplitude_bound s.1 s.2 (hA s).1 (hA s).2
      (σ y) hnorm.le z hz).trans (hAC s hs)
  · rw [polynomialWord_generatorScheme_eq a p.1 hBracket hGroup]
    exact he

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

/-- Fixed-time continuity survives concatenation even when endpoints vary. -/
theorem continuous_path_trans_sample {Y : Type} [TopologicalSpace Y]
    {a b c : Y → X} (p : ∀ y, Path (a y) (b y)) (q : ∀ y, Path (b y) (c y))
    (hp : ∀ t, Continuous (fun y => p y t)) (hq : ∀ t, Continuous (fun y => q y t))
    (t : unitInterval) : Continuous (fun y => ((p y).trans (q y)) t) := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simpa only [Path.trans_apply, dite_eq_left ht] using
      hp ⟨2 * (t : ℝ), unitInterval.mul_pos_mem_iff zero_lt_two |>.mpr ⟨t.property.1, ht⟩⟩
  · simpa only [Path.trans_apply, dite_eq_right ht] using
      hq ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.mpr
        ⟨(not_le.mp ht).le, t.property.2⟩⟩

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportVisitPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outward, switch, and return paths

The actual three curves are concatenated, retaining their exact heights and
the logarithmic switch error. This statement is independent of how the
switch estimate is obtained and is used below for the Cartan root curves.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped unitInterval

variable {G W : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [AddCommGroup W] [Module ℝ W]

omit [IsIsometricSMul G G] in
/-- Every fixed time sample depends continuously on the initial sheet and
the switch amplitude. -/
theorem continuous_supportVisitPath_sample
    (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    {Y : Type} [TopologicalSpace Y] (n : Y → G) (hn : Continuous n)
    (b : Y → ℝ) (hb : Continuous b) (d₀ : G) (r : ℝ) (t : unitInterval) :
    Continuous (fun y => supportVisitPath d hd hzero f hf hf₀ (n y) d₀ r (b y) t) := by
  let p₀ y := flowPath d hd hzero (n y * d₀) r
  let p₁ y := flowPath d hd hzero (n y * f (b y) * d₀) r
  let q (y : Y) : Path ((n y * d₀) * d r) ((n y * f (b y) * d₀) * d r) := {
    toFun := fun t => n y * f ((t : ℝ) * b y) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  have hp₀ (u : unitInterval) : Continuous (fun y => p₀ y u) := by
    change Continuous (fun y => (n y * d₀) * d (r * (u : ℝ)))
    exact (hn.mul_const d₀).mul_const _
  have hp₁ (u : unitInterval) : Continuous (fun y => (p₁ y).symm u) := by
    change Continuous (fun y => (n y * f (b y) * d₀) * d (r * (unitInterval.symm u : ℝ)))
    exact ((hn.mul (hf.comp hb)).mul_const d₀).mul_const _
  have hq (u : unitInterval) : Continuous (fun y => q y u) := by
    change Continuous (fun y => n y * f ((u : ℝ) * b y) * (d₀ * d r))
    exact (hn.mul (hf.comp (continuous_const.mul hb))).mul_const _
  exact continuous_path_trans_sample (fun y => (p₀ y).trans (q y)) (fun y => (p₁ y).symm)
    (fun u => continuous_path_trans_sample p₀ q hp₀ hq u) hp₁ t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ParametrizedSupportPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous sampling of prescribed generator words

When the generator indices are fixed and the amplitudes depend continuously
on a parameter, every fixed time sample of the explicitly constructed path
is continuous in that parameter. This retains the measurability needed for
stationary endpoint averaging.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G I : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1)
  (d₀ : G) (r : ℝ)

/-- Fixed-time samples of a word path are continuous under continuous
variation of its amplitudes and its initial sheet. -/
theorem continuous_supportWordPath_sample
    {Y : Type} [TopologicalSpace Y] (w : List (I × (Y → ℝ)))
    (hw : ∀ z ∈ w, Continuous z.2) (n : Y → G) (hn : Continuous n)
    (t : unitInterval) :
    Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ d₀ r
      (w.map (fun z => (z.1, z.2 y))) (n y) t) := by
  induction w generalizing n t with
  | nil =>
    change Continuous (fun y => n y * d₀)
    exact hn.mul_const d₀
  | cons z w ih =>
    rcases z with ⟨i, b⟩
    have hb : Continuous b := hw (i, b) List.mem_cons_self
    have hw' : ∀ z ∈ w, Continuous z.2 := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    change Continuous (fun y =>
      ((supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) (n y) d₀ r (b y)).trans
        (supportWordPath d f hd hf hd₀ hf₀ d₀ r
          (w.map (fun z => (z.1, z.2 y))) (n y * f i (b y)))) t)
    apply continuous_path_trans_sample
    · intro u
      exact continuous_supportVisitPath_sample (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n hn b hb d₀ r u
    · intro u
      exact ih hw' (fun y => n y * f i (b y)) (hn.mul ((hf i).comp hb)) u

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ParametrizedGeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous path samples for the finite generator schemes

The conjugating letters are fixed. Only the inserted amplitudes vary, so
the whole expanded word has a fixed combinatorial pattern and continuous
amplitudes. This makes each of its support-path samples continuous.
-/

noncomputable section

namespace PolycyclicRecognition

variable {I Y : Type} {k : ℕ}

theorem parameterGeneratorSchemeWord_eval (w : Fin k → List (I × ℝ)) (i : Fin k → I)
    (σ : Y → Fin k → ℝ) (y : Y) :
    (parameterGeneratorSchemeWord w i σ).map (fun z => (z.1, z.2 y)) =
      generatorSchemeWord w i (σ y) := by
  simp [parameterGeneratorSchemeWord, generatorSchemeWord, List.map_flatten,
    List.map_ofFn, List.map_map, Function.comp_def]

variable [TopologicalSpace Y]

theorem parameterGeneratorSchemeWord_continuous (w : Fin k → List (I × ℝ))
    (i : Fin k → I) (σ : Y → Fin k → ℝ) (hσ : Continuous σ) :
    ∀ z ∈ parameterGeneratorSchemeWord w i σ, Continuous z.2 := by
  intro z hz
  obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
  have hconst (v : List (I × ℝ)) (z : I × (Y → ℝ))
      (hz : z ∈ v.map (fun a => (a.1, fun _ : Y => a.2))) : Continuous z.2 := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    exact continuous_const
  rcases List.mem_append.mp hz with hz | hz
  · rcases List.mem_append.mp hz with hz | hz
    · exact hconst _ z hz
    · have he : z = (i j, fun y => σ y j) := by simpa using hz
      rw [he]
      exact (continuous_apply j).comp hσ
  · exact hconst _ z hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledUniformGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform generator words in the actual rescaled Lie model

The compact-family theorem is transported back through the actual coordinate
bases. Finiteness of the word-basis choices gives bounds independent of the
maximizing basis, scale, and generator exponents.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

variable {I L G : Type} [LieRing L] [LieAlgebra ℝ L] [Group G]

/-- Direct polynomial evaluation transports to the actual group word. -/
theorem basis_polynomialWord {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (w : List (I × ℝ)) :
    Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (basisBracket b))
      (fun i => b.equivFun (X i)) w)) = generatorGroupWord X Exp w := by
  have hp (x y : Fin n → ℝ) :
      Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
        Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm]
  induction w with
  | nil => simp only [polynomialWord, map_zero, generatorGroupWord_nil, hzero]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    rw [polynomialWord, hp, ih, map_smul, LinearEquiv.symm_apply_apply,
      generatorGroupWord_cons]

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledInverseSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous endpoint coding in actual rescaled Lie coordinates

The compact normalized laws give a common coordinate ball and continuous
inverse schemes. Transport through each actual rescaled basis preserves the
endpoint identities and gives uniform bounds across all maximizing bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Metric
open scoped BigOperators

variable {I L G : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [Fintype I] [DecidableEq I]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A continuous inverse generator scheme on one common ball in each
actual rescaled logarithm chart. All constants are independent of scale,
generator exponents, and maximizing word basis. -/
theorem exists_uniform_rescaled_inverse_sections (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (s : I → ℝ) (β : WordBasisSelections X (boundedBracketWords k)),
        IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
          (fun w => bracketWordExponent s w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
          (fun j => bracketWordExponent s (β.val j)) r
        ∃ (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I)
          (σ : (Fin (finrank ℝ L) → ℝ) → Fin (finrank ℝ L) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ L) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * s i) • X i) Exp
              (generatorSchemeWord w i (σ y)) = Exp (b.equivFun.symm y) := by
  classical
  obtain ⟨C₀, _, hc⟩ := exists_rescaledExponentialData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  let S := boundedBracketWords (I := I) k
  let bstd := Pi.basisFun ℝ (Fin (finrank ℝ L))
  have hf (β : WordBasisSelections X S) := exists_uniform_bounded_coordinate_inverse
    a bstd (fun j => (β.val j : FreeMagma I)) C₀ (finrank ℝ L) (by simp)
  choose ε N C hε hC hsections using hf
  obtain ⟨ε', hε', hεle⟩ := finite_positive_lower_bound Finset.univ ε (fun β _ => hε β)
  let N' := ∑ β : WordBasisSelections X S, N β
  let C' := 1 + ∑ β : WordBasisSelections X S, C β
  have hCnonneg β : 0 ≤ C β := (by norm_num : (0 : ℝ) ≤ 1).trans (hC β)
  have hC' : 1 ≤ C' := by
    dsimp [C']
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun β _ => hCnonneg β))
  refine ⟨ε', N', C', hε', hC', ?_⟩
  intro s β hβ r hr b
  have hp : rescaledLieData X S β s r ∈
      normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I)) bstd C₀ := by
    have hbstd : (bstd : Fin (finrank ℝ L) → (Fin (finrank ℝ L) → ℝ)) =
        fun j => Pi.single j 1 := by
      funext j
      exact Pi.basisFun_apply ℝ _ j
    rw [hbstd]
    exact hc s β hβ r hr
  have hsec := hsections β _ hp
  obtain ⟨w, i, σ, hσ, hright⟩ := hsec
  have hsub : ball (0 : Fin (finrank ℝ L) → ℝ) ε' ⊆ ball 0 (ε β) :=
    ball_subset_ball (hεle β (Finset.mem_univ β))
  refine ⟨w, i, σ, hσ.mono hsub, ?_⟩
  intro y hy
  obtain ⟨hnorm, hlen, hamp, he⟩ := hright y (hsub hy)
  refine ⟨hnorm, hlen.trans ?_, ?_, ?_⟩
  · exact Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ β)
  · intro z hz
    have hb : C β ≤ C' := by
      have hs : C β ≤ ∑ γ : WordBasisSelections X S, C γ :=
        Finset.single_le_sum (fun γ _ => hCnonneg γ) (Finset.mem_univ β)
      dsimp [C']
      linarith
    exact (hamp z hz).trans hb
  · have hw := basis_polynomialWord b Exp hzero a hm
      (fun i => Real.exp (r * s i) • X i) (generatorSchemeWord w i (σ y))
    change Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (rescaledLieData X S β s r).1)
      (rescaledLieData X S β s r).2 (generatorSchemeWord w i (σ y)))) = _ at hw
    rw [he] at hw
    exact hw.symm

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_VolumeExponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting exponential volume rates

A polynomial loss in the cardinality of a separated set does not change
its exponential rate. This is the limiting step after applying the path
packing estimate to the good endpoint set selected by stationary averaging.
-/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- An eventual exponential lower bound cannot exceed an exponential upper
bound with a fixed polynomial prefactor. -/
theorem exponent_le_of_polynomial_exp_bound
    {p q c C : ℝ} (hc : 0 < c) (hC : 0 < C) (k : ℕ)
    (hbound : ∀ᶠ r : ℝ in atTop,
      c * Real.exp (r * p) ≤ C * (1 + r) ^ k * Real.exp (r * q)) :
    p ≤ q := by
  have hlog : Tendsto (fun r : ℝ => Real.log (1 + r) / r) atTop (𝓝 0) := by
    have ha : Tendsto (fun r : ℝ => 1 + r) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b - 1)] with r hr
      linarith
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      ha
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    congr 1 <;> ring
  have hconst : Tendsto (fun r : ℝ => (Real.log C - Real.log c) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto
      (fun r : ℝ => q + (Real.log C - Real.log c) / r + (k : ℝ) * (Real.log (1 + r) / r))
      atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds.add hconst).add (tendsto_const_nhds.mul hlog)
  apply ge_of_tendsto hlim
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have h1 : 0 < 1 + r := by linarith
  have h := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hr
  rw [Real.log_mul hc.ne' (Real.exp_ne_zero _),
    Real.log_mul (mul_ne_zero hC.ne' (pow_ne_zero _ h1.ne')) (Real.exp_ne_zero _),
    Real.log_mul hC.ne' (pow_ne_zero _ h1.ne'), Real.log_pow,
    Real.log_exp, Real.log_exp] at h
  calc
    p ≤ (q * r + (Real.log C - Real.log c) + (k : ℝ) * Real.log (1 + r)) / r :=
      (le_div_iff₀ hr0).mpr (by nlinarith [h])
    _ = _ := by field_simp

end PolycyclicRecognition

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

/-- Positive exponential lower mass and a polynomial exponential upper
cardinality force the comparison of their exponents. -/
theorem exponent_le_of_separated_card_bounds {p q a D : ℝ}
    (ha : 0 < a) (hD : 0 < D) {Q : ℝ≥0∞} (hQ : Q < ⊤) (k : ℕ)
    (h : ∀ᶠ r : ℝ in atTop, ∃ N : ℕ,
      ENNReal.ofReal a * ENNReal.ofReal (Real.exp (r * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply exponent_le_of_polynomial_exp_bound ha (show 0 < D * Q.toReal + 1 by positivity) k
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  obtain ⟨N, hlow, hupp⟩ := hr
  have hfinite : (N : ℝ≥0∞) * Q ≠ ⊤ := ENNReal.mul_ne_top (by simp) hQ.ne
  have hreal := ENNReal.toReal_mono hfinite hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_natCast] at hreal
  calc
    a * Real.exp (r * p) ≤ (N : ℝ) * Q.toReal := hreal
    _ ≤ (D * (1 + r) ^ k * Real.exp (r * q)) * Q.toReal :=
      mul_le_mul_of_nonneg_right hupp ENNReal.toReal_nonneg
    _ = (D * Q.toReal) * (1 + r) ^ k * Real.exp (r * q) := by ring
    _ ≤ _ := by gcongr; linarith

/-- The same comparison with a positive finite lower mass coefficient. -/
theorem exponent_le_of_separated_mass_bounds {p q D : ℝ}
    {a Q : ℝ≥0∞} (ha : 0 < a) (hafin : a < ⊤) (hD : 0 < D) (hQ : Q < ⊤) (k : ℕ)
    (h : ∀ᶠ r : ℝ in atTop, ∃ N : ℕ,
      a * ENNReal.ofReal (Real.exp (r * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply exponent_le_of_separated_card_bounds
    (ENNReal.toReal_pos ha.ne' hafin.ne) hD hQ k
  simpa only [ENNReal.ofReal_toReal hafin.ne] using h

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting one map that is good on a finite mesh

The stationary volume comparison samples endpoints independently of the
stationary map. Uniform `L²` bounds at finitely many sampled path points
give a single map for which most endpoints have every sampled error small.
The finite mesh is fixed before the scale tends to infinity.
-/

namespace PolycyclicRecognition

open MeasureTheory
open scoped ENNReal

/-- Chebyshev and the finite union bound for a fixed mesh. -/
theorem measure_bad_mesh_le
    {I Z E : Type} [Fintype I] [MeasurableSpace Z] [NormedAddCommGroup E]
    (μ : Measure Z) (f : I → Z → E) (hfm : ∀ i, AEMeasurable (fun z => ‖f i z‖ₑ) μ) {η a : ℝ≥0∞}
    (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hbound : ∀ i, eLpNorm (f i) 2 μ ≤ a) :
    μ {z | ∃ i, η ≤ ‖f i z‖ₑ} ≤ (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) := by
  have hbad : {z | ∃ i, η ≤ ‖f i z‖ₑ} = ⋃ i, {z | η ≤ ‖f i z‖ₑ} := by
    ext z
    simp
  rw [hbad]
  calc
    μ (⋃ i, {z | η ≤ ‖f i z‖ₑ}) ≤ ∑ i, μ {z | η ≤ ‖f i z‖ₑ} :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : I, η⁻¹ ^ 2 * a ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := meas_ge_le_mul_pow_eLpNorm_enorm (hf := (hfm i).aestronglyMeasurable) (p := 2) μ
        (by norm_num) (by norm_num) (f := fun z => ‖f i z‖ₑ) hη (fun h => (hηtop h).elim)
      simp only [enorm_enorm, eLpNorm_enorm, ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
      apply h.trans
      gcongr
      exact hbound i
    _ = _ := by simp [nsmul_eq_mul]

/-- A set of small product measure has a small fiber over some point of a
probability space. This selects the map after endpoint averaging. -/
theorem exists_fiber_measure_lt
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [SFinite ν]
    (s : Set (X × Y)) (hs : MeasurableSet s) {t : ℝ≥0∞}
    (hsmall : (μ.prod ν) s < t) :
    ∃ x, ν {y | (x, y) ∈ s} < t := by
  by_contra h
  push Not at h
  have hi : t ≤ ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ := by
    calc
      t = ∫⁻ _x, t ∂μ := by simp
      _ ≤ _ := lintegral_mono h
  rw [Measure.prod_apply hs] at hsmall
  exact (not_le_of_gt hsmall) hi

/-- Uniform `L²` estimates at each sampled point provide one stationary map
with an exceptional endpoint set of arbitrarily prescribed small measure. -/
theorem exists_good_mesh_fiber
    {I X Y E : Type} [Fintype I] [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : I → X × Y → E) (hf : ∀ i, Measurable (f i))
    {η a t : ℝ≥0∞} (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hbound : ∀ i y, eLpNorm (fun x => f i (x, y)) 2 μ ≤ a)
    (hsmall : (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) < t) :
    ∃ x, ν {y | ∃ i, η ≤ ‖f i (x, y)‖ₑ} < t := by
  let s : Set (X × Y) := {z | ∃ i, η ≤ ‖f i z‖ₑ}
  have hs : MeasurableSet s := by
    have heq : s = ⋃ i, {z | η ≤ ‖f i z‖ₑ} := by ext z; simp [s]
    rw [heq]
    exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (hf i).enorm)
  apply exists_fiber_measure_lt μ ν s hs
  apply lt_of_le_of_lt _ hsmall
  rw [Measure.prod_apply_symm hs]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν) ≤
        ∫⁻ _y, (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * a ^ 2) ∂ν := by
      apply lintegral_mono
      intro y
      exact measure_bad_mesh_le μ (fun i x => f i (x, y))
        (fun i => ((hf i).comp measurable_prodMk_right).enorm.aemeasurable) hη hηtop
        (fun i => hbound i y)
    _ = _ := by simp

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PairPathMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed meshes and height control of image paths

The mesh depends only on the requested error and the common path-length
constant, not on the scale or on the endpoint. The actual `L²` height cocycle
controls its finitely many samples; the common Lipschitz bounds then control
every point of the image path.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace PolycyclicRecognition

/-- A single finite mesh for the unit path interval. -/
theorem exists_fixed_path_mesh {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Set.Icc (0 : ℝ) 1),
      ∀ t, ∃ u ∈ S, dist t u ≤ δ := by
  classical
  obtain ⟨S, _, hS, hcover⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) 1)).finite_cover_balls hδ
  refine ⟨hS.toFinset, ?_⟩
  intro t
  obtain ⟨u, hu, htu⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ t))
  exact ⟨u, hS.mem_toFinset.mpr hu, (Metric.mem_ball.mp htu).le⟩

variable {G W T : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoMetricSpace T]
  {Λ : ℝ≥0}

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]

omit [IsIsometricSMul G G] in
/-- The norm in the actual Hilbert space equals the `L²` seminorm of the
pointwise height error; there is no choice of pointwise representatives here. -/
theorem eLpNorm_pairHeight_error
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    eLpNorm (fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd) 2 μ =
      ENNReal.ofReal ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)).sub
    (Lp.coeFn_const 2 μ (l g).toAdd)).symm.trans
      (Lp.coeFn_sub _ _).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathMesh
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite meshes for paths with short jumps

The support-switch construction has a bounded number of logarithmically
short switches. An additive coarse error in its parameterized path therefore
contributes only the corresponding additive error to the height comparison.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W T : Type} [Group G] [MetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoMetricSpace T] {Λ : ℝ≥0}

/-- Sampled height estimates control a whole coarse path, retaining the
additive distance error explicitly. -/
theorem coarse_image_path_height_control
    (p : NormalizedPair G Λ) (π : G →* Multiplicative W) (l : G →* Multiplicative W)
    {Lπ L r δ η ε κ : ℝ} (hLπ : 0 ≤ Lπ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Lπ * dist x y)
    (γ : T → G) (hγ : ∀ t u, dist (γ t) (γ u) ≤ L * r * dist t u + κ)
    (S : Finset T) (hmesh : ∀ t, ∃ u ∈ S, dist t u ≤ δ)
    (E : Set W)
    (hheight : ∀ u ∈ S, ∃ w ∈ E, ‖(l (γ u)).toAdd - r • w‖ ≤ ε * r)
    (herror : ∀ u ∈ S, ‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ ≤ η * r) :
    ∀ t, ∃ w ∈ E,
      ‖pairHeight π (γ t) p - r • w‖ ≤
        (Lπ * Λ * L * δ + η + ε) * r + Lπ * Λ * κ := by
  intro t
  obtain ⟨u, hu, htu⟩ := hmesh t
  obtain ⟨w, hw, hwu⟩ := hheight u hu
  refine ⟨w, hw, ?_⟩
  have hdist : dist (γ t) (γ u) ≤ L * r * δ + κ :=
    (hγ t u).trans (by
      linarith [mul_le_mul_of_nonneg_left htu (mul_nonneg hL hr)])
  have hF := p.property.1.1.dist_le_mul (γ t) (γ u)
  have hp : ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ ≤
      Lπ * Λ * (L * r * δ + κ) := by
    apply (hπ (p.val.1 (γ t)) (p.val.1 (γ u))).trans
    calc
      _ ≤ Lπ * (Λ * dist (γ t) (γ u)) := mul_le_mul_of_nonneg_left hF hLπ
      _ ≤ Lπ * (Λ * (L * r * δ + κ)) := by gcongr
      _ = _ := by ring
  have triangle (a b c : W) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  calc
    _ ≤ ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ +
        ‖pairHeight π (γ u) p - r • w‖ := triangle _ _ _
    _ ≤ Lπ * Λ * (L * r * δ + κ) +
        (‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ +
          ‖(l (γ u)).toAdd - r • w‖) := add_le_add hp (triangle _ _ _)
    _ ≤ Lπ * Λ * (L * r * δ + κ) + (η * r + ε * r) :=
      add_le_add le_rfl (add_le_add (herror u hu) hwu)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoarsePathRadius
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radius control for logarithmic-error paths

The support-path parameter bounds imply a single linear ambient ball bound
for every sample, uniformly at all scales at least one.
-/

namespace PolycyclicRecognition

variable {X : Type} [PseudoMetricSpace X] {x y : X}

/-- A coarse path stays within its speed plus its additive error of its source. -/
theorem PathMetricBound.dist_source_le {p : Path x y} {L κ : ℝ}
    (h : PathMetricBound p L κ) (hL : 0 ≤ L) (t : unitInterval) :
    dist x (p t) ≤ L + κ := by
  have hb := h 0 t
  rw [Path.source, Set.Icc.coe_zero, zero_sub, abs_neg,
    abs_of_nonneg t.property.1] at hb
  exact hb.trans (by nlinarith [t.property.2])

/-- The logarithmic error is uniformly at most a linear error for `r ≥ 1`. -/
theorem PathMetricBound.dist_source_le_linear {p : Path x y} {C r : ℝ}
    (h : PathMetricBound p (C * r) (C * (1 + Real.log (2 + r))))
    (hC : 0 ≤ C) (hr : 1 ≤ r) (t : unitInterval) :
    dist x (p t) ≤ (4 * C) * r := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
  have hb := h.dist_source_le (mul_nonneg hC (by linarith)) t
  have hh : 1 + Real.log (2 + r) ≤ 3 * r := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hC
  nlinarith

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NormalizedEndpointMeasure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized measure on an independent endpoint domain

Normalizing the restricted coordinate measure produces a probability on
the endpoint subtype. A bad set of probability below one half leaves at
least half of the original coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {V : Type} [MeasurableSpace V]

theorem normalizedEndpointMeasure_isProbability (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤) :
    IsProbabilityMeasure (normalizedEndpointMeasure μ S) := by
  constructor
  rw [normalizedEndpointMeasure, Measure.smul_apply, smul_eq_mul,
    comap_subtype_coe_apply hS, image_univ, Subtype.range_coe]
  exact ENNReal.inv_mul_cancel h₀ hfin

/-- Recover original coordinate volume from the normalized probability. -/
theorem endpoint_volume_eq_mass_mul_probability (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤) (A : Set S) :
    μ (Subtype.val '' A) = μ S * normalizedEndpointMeasure μ S A := by
  rw [normalizedEndpointMeasure, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel h₀ hfin, one_mul, comap_subtype_coe_apply hS]

/-- The good endpoints retain half the original coordinate mass. -/
theorem half_volume_le_good_endpoints (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤)
    {B : Set S} (hB : MeasurableSet B)
    (hbad : normalizedEndpointMeasure μ S B < 1 / 2) :
    μ S * (1 / 2) ≤ μ (Subtype.val '' Bᶜ) := by
  let ν := normalizedEndpointMeasure μ S
  let : IsProbabilityMeasure ν := normalizedEndpointMeasure_isProbability μ hS h₀ hfin
  have hh : (1 / 2 : ℝ≥0∞) ≤ ν Bᶜ := by
    have he := prob_add_prob_compl (μ := ν) hB
    have hb : ν B ≤ 1 / 2 := hbad.le
    have hsum : (1 / 2 : ℝ≥0∞) + 1 / 2 ≤ 1 / 2 + ν Bᶜ := by
      calc
        _ = 1 := ENNReal.add_halves _
        _ = ν B + ν Bᶜ := he.symm
        _ ≤ _ := add_le_add hb le_rfl
    exact (ENNReal.add_le_add_iff_left (by norm_num)).mp hsum
  rw [endpoint_volume_eq_mass_mul_probability μ hS h₀ hfin Bᶜ]
  exact mul_le_mul' le_rfl hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationarySampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-mesh sampling at large scale

A sublinear L² estimate on growing balls selects one actual pair with
small errors for most endpoints of a fixed finite family of sampled paths.
The finite mesh is chosen before the scale tends to infinity.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace PolycyclicRecognition

/-- The finite-union Chebyshev bound can be made smaller than one half by
choosing a single positive L² tolerance, independently of scale. -/
theorem exists_mesh_tolerance (M : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ (M : ℝ≥0∞) *
      ((ENNReal.ofReal η)⁻¹ ^ 2 * ENNReal.ofReal δ ^ 2) < 1 / 2 := by
  have hη0 : ENNReal.ofReal η ≠ 0 := (ENNReal.ofReal_pos.mpr hη).ne'
  have hc : (M : ℝ≥0∞) * (ENNReal.ofReal η)⁻¹ ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hη0))
  have ht : Filter.Tendsto (fun n : ℕ => (M : ℝ≥0∞) * (ENNReal.ofReal η)⁻¹ ^ 2 *
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
    have hp := ENNReal.Tendsto.pow (n := 2)
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa using ENNReal.Tendsto.const_mul hp (Or.inr hc)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1 / 2))).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, by simpa [mul_assoc] using hn⟩

/-- For all sufficiently large scales there is a single normalized pair
whose normalized errors are small at every mesh point for more than half
the endpoints. No pointwise supremum over a path is used. -/
theorem eventually_exists_pair_good_on_mesh
    {G W I Y : Type} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    [Fintype I] [MeasurableSpace Y]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (γ : ℝ → Y → I → G) (hγ : ∀ r i, Measurable (fun y => γ r y i))
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ r, 1 ≤ r → ∀ y i, dist 1 (γ r y i) ≤ R * r)
    {η : ℝ} (hη : 0 < η) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∃ p : NormalizedPair G Λ,
      ν {y | ∃ i, ENNReal.ofReal η ≤
        ‖r⁻¹ • (pairHeight π (γ r y i) p - (l (γ r y i)).toAdd)‖ₑ} < 1 / 2 := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_mesh_tolerance (Fintype.card I) hη
  obtain ⟨r₁, _hr₁, hbound⟩ := uniform_sublinear_on_balls (fun g : G => dist 1 g) hsub hR δ hδ
  refine ⟨max 1 r₁, le_max_left _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let f : I → NormalizedPair G Λ × Y → W := fun i z =>
    r⁻¹ • (pairHeight π (γ r z.2 i) z.1 - (l (γ r z.2 i)).toAdd)
  have hf (i : I) : Measurable (f i) := by
    exact (((continuous_pairHeight π hπ).measurable.comp
      (((hγ r i).comp measurable_snd).prodMk measurable_fst)).sub
      (hl.measurable.comp ((hγ r i).comp measurable_snd))).const_smul _
  apply exists_good_mesh_fiber μ ν f hf
    (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top _ hsmall
  intro i y
  have hb := hbound r ((le_max_right _ _).trans hr) (γ r y i) (hball r hr1 y i)
  change eLpNorm (r⁻¹ • (fun p : NormalizedPair G Λ =>
    pairHeight π (γ r y i) p - (l (γ r y i)).toAdd)) 2 μ ≤ ENNReal.ofReal δ
  rw [eLpNorm_const_smul, eLpNorm_pairHeight_error μ π hπ l, ← ofReal_norm,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hrpos.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ r⁻¹ * (δ * r) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hrpos.le)
    _ = δ := by field_simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryPathSampling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stationary sampling along controlled paths

A fixed finite mesh selects one normalized pair good for most independently
sampled endpoints. The coarse metric bound extends that mesh estimate to the
whole image path and retains the logarithmic error explicitly.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

variable {G W Y : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace Y]

/-- The finite-mesh bad set has mass less than one half; outside it every
point of the image path has controlled height. No supremum-in-`L²` is used. -/
theorem eventually_exists_pair_good_on_paths
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    {K C δ η : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 < η)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (endpoint : ℝ → Y → G)
    (γ : ∀ r y, Path (1 : G) (endpoint r y))
    (hγ : ∀ r t, Measurable (fun y => γ r y t))
    (hpath : ∀ r, 1 ≤ r → ∀ y,
      PathMetricBound (γ r y) (C * r) (C * (1 + Real.log (2 + r))))
    (E : Set W)
    (hheight : ∀ r, 1 ≤ r → ∀ y t, ∃ w ∈ E, (l (γ r y t)).toAdd = r • w) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (B : Set Y),
      MeasurableSet B ∧ ν B < 1 / 2 ∧ ∀ y ∉ B, ∀ t,
        ∃ w ∈ E, ‖pairHeight π (γ r y t) p - r • w‖ ≤
          (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  obtain ⟨S, hS⟩ := exists_fixed_path_mesh hδ
  let sample (r : ℝ) (y : Y) (i : S) := γ r y i.val
  obtain ⟨r₀, hr₀, hgood⟩ := eventually_exists_pair_good_on_mesh μ ν π l hπ hl hsub
    sample (fun r i => hγ r i.val) (by positivity : 0 ≤ 4 * C)
    (fun r hr y i => (hpath r hr y).dist_source_le_linear hC hr i.val) hη
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  obtain ⟨p, hp⟩ := hgood r hr
  let B : Set Y := {y | ∃ i : S, ENNReal.ofReal η ≤
    ‖r⁻¹ • (pairHeight π (sample r y i) p - (l (sample r y i)).toAdd)‖ₑ}
  have hB : MeasurableSet B := by
    dsimp only [B]
    simp only [ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_le measurable_const
    exact ((((continuous_pairHeight π hπ).measurable.comp
      ((hγ r i.val).prodMk measurable_const)).sub
      (hl.measurable.comp (hγ r i.val))).const_smul r⁻¹).enorm
  refine ⟨p, B, hB, hp, ?_⟩
  intro y hy
  have herr (u : unitInterval) (hu : u ∈ S) :
      ‖pairHeight π (γ r y u) p - (l (γ r y u)).toAdd‖ ≤ η * r := by
    have hn : ¬ ENNReal.ofReal η ≤
        ‖r⁻¹ • (pairHeight π (sample r y ⟨u, hu⟩) p -
          (l (sample r y ⟨u, hu⟩)).toAdd)‖ₑ := fun hh => hy ⟨⟨u, hu⟩, hh⟩
    have hlt := lt_of_not_ge hn
    rw [← ofReal_norm] at hlt
    have hh := (ENNReal.ofReal_lt_ofReal_iff hη).mp hlt
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)] at hh
    have hm := mul_le_mul_of_nonneg_left hh.le hrpos.le
    simpa only [sample, ← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul, mul_comm r η] using hm
  have hcontrol := coarse_image_path_height_control (ε := 0) p π l hK hC hrpos.le hLip
    (γ r y) (fun t u => by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hpath r hr1 y t u)
    S hS E (fun u _ => by
      obtain ⟨w, hw, he⟩ := hheight r hr1 y u
      exact ⟨w, hw, by simp [he]⟩) herr
  intro t
  obtain ⟨w, hw, hb⟩ := hcontrol t
  refine ⟨w, hw, ?_⟩
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CoordinateStationaryPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent coordinate sampling for nonnegative path families

This bridge normalizes coordinate volume once and extends a family from
nonnegative scales. It separates finite-measure sampling from the Lie
coordinate constructions that supply the paths.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {G W : Type} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Continuous coding on a common coordinate ball supplies a good endpoint
set of at least half its volume at every sufficiently large scale. -/
theorem coordinate_stationary_paths {n : ℕ} {ε C K : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ η * dist 1 g + B)
    (E : Set W)
    (endpoint : ℝ → ball (0 : Fin n → ℝ) ε → G)
    (hcode : ∀ r : ℝ, 0 ≤ r → ∃ γ : ∀ y, Path (1 : G) (endpoint r y),
      (∀ t, Continuous (fun y => γ y t)) ∧
      (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
      ∀ y t, ∃ w ∈ E, (l (γ y t)).toAdd = r • w) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (B : Set (ball (0 : Fin n → ℝ) ε)),
        MeasurableSet B ∧ volume (ball (0 : Fin n → ℝ) ε) * (1 / 2) ≤ volume (Subtype.val '' Bᶜ) ∧
        ∀ y ∉ B, ∃ γ : Path (1 : G) (endpoint r y),
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ w ∈ E, ‖pairHeight π (γ t) p - r • w‖ ≤
            (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  let V := Fin n → ℝ
  let S := ball (0 : V) ε
  let Y := S
  have hS : MeasurableSet S := measurableSet_ball
  have hS₀ : volume S ≠ 0 := (measure_ball_pos volume (0 : V) hε).ne'
  have hSfin : volume S ≠ ⊤ := ne_of_lt <|
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : V) ε).measure_lt_top
  let ν := normalizedEndpointMeasure volume S
  let : IsProbabilityMeasure ν := normalizedEndpointMeasure_isProbability volume hS hS₀ hSfin
  choose γ hγ hb hh using (fun r : ℝ => hcode (max 0 r) (le_max_left _ _))
  intro δ hδ η hη
  obtain ⟨r₀, hr₀, hgood⟩ := eventually_exists_pair_good_on_paths μ ν π l hπ hl hsub
    hK hC hδ hη hLip (fun r => endpoint (max 0 r)) γ (fun r t => (hγ r t).measurable)
    (fun r hr y => by simpa only [max_eq_right (by linarith : 0 ≤ r)] using hb r y)
    E (fun r hr y t => by simpa only [max_eq_right (by linarith : 0 ≤ r)] using hh r y t)
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨p, B, hB, hmass, hheight⟩ := hgood r hr
  refine ⟨p, B, hB, half_volume_le_good_endpoints volume hS hS₀ hSfin hB hmass, ?_⟩
  intro y hy
  have he : max 0 r = r := max_eq_right (by linarith [hr₀.trans hr])
  refine ⟨(γ r y).cast rfl (by rw [he]), ?_, hheight y hy⟩
  have hm : PathMetricBound (γ r y) (C * r) (C * (1 + Real.log (2 + r))) := by
    simpa only [he] using hb r y
  exact hm.cast rfl (by rw [he])

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

variable [TopologicalSpace N] [ContinuousMul G]

omit [IsIsometricSMul G G] [MeasurableMul N] [ContinuousMul G] in
/-- A closed subgroup realization gives a finite packing constant at every
fixed radius, since the ambient metric is proper. -/
theorem fixedSlice_packing_constant_lt_top
    [ProperSpace G] (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (hι : Topology.IsClosedEmbedding ι) (r : ℝ) :
    μ (ι ⁻¹' closedBall (1 : G) r) < ⊤ :=
  (hι.isProperMap.isCompact_preimage (isCompact_closedBall 1 r)).measure_lt_top

end PolycyclicRecognition

end

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

section Finite

variable [DecidableEq G]

/-- The image of a sufficiently separated finite set has the same cardinality. -/
theorem normalizedPair_card_image (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    (s.image p.val.1).card = s.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro x hx y hy he
  by_contra hne
  have h := normalizedPair_image_dist_gt_one p hΛ (hsep x hx y hy hne)
  rw [he, dist_self] at h
  linarith

/-- Unit separation is preserved on the image finite set. -/
theorem normalizedPair_image_separated (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    ∀ x ∈ s.image p.val.1, ∀ y ∈ s.image p.val.1, x ≠ y → 1 ≤ dist x y := by
  classical
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := fun he => hxy (congrArg p.val.1 he)
  exact (normalizedPair_image_dist_gt_one p hΛ (hsep a ha b hb hab)).le

end Finite

/-- The image path is based at the identity by normalization, and both
coarse metric constants are multiplied by the same Lipschitz constant. -/
theorem normalizedPair_map_path (p : NormalizedPair G Λ) {g : G}
    (γ : Path (1 : G) g) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    ∃ η : Path (1 : G) (p.val.1 g),
      (∀ t, η t = p.val.1 (γ t)) ∧ PathMetricBound η (Λ * L) (Λ * κ) := by
  let η := (γ.map p.val.1.continuous).cast p.property.2.symm rfl
  refine ⟨η, (fun _ => rfl), ?_⟩
  intro s t
  change dist (p.val.1 (γ s)) (p.val.1 (γ t)) ≤ _
  calc
    _ ≤ (Λ : ℝ) * dist (γ s) (γ t) := p.property.1.1.dist_le_mul _ _
    _ ≤ (Λ : ℝ) * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) Λ.coe_nonneg
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_PathVolumeComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stationary path-volume comparison

A common pair on a positive-volume endpoint set gives the lower exponential
count. Coarse path packing bounds its image count. Polynomial and logarithmic
losses disappear before the template thickening tends to zero.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric Set
open scoped NNReal ENNReal Topology Pointwise

variable {G W : Type} [Group G] [MetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : ℝ≥0}

/-- Exact comparison with every positive enlargement of the image template. -/
theorem exponent_le_of_stationary_path_counts
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    {p K C D : ℝ} {a Q : ℝ≥0∞} (hΛ : 0 < (Λ : ℝ))
    (hK : 0 ≤ K) (hC : 0 ≤ C) (ha : 0 < a) (hafin : a < ⊤)
    (hQ : Q < ⊤) (hD : 0 < D) (k : ℕ)
    (hlower : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (f : NormalizedPair G Λ) (s : Finset G),
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) ∧
        a * ENNReal.ofReal (Real.exp (r * p)) ≤ (s.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ s, ∃ γ : Path (1 : G) g,
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ z ∈ E, ‖pairHeight π (γ t) f - r • z‖ ≤
            (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)))
    (hupper : ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∀ ε : ℝ, 0 < ε → p ≤ P (E + closedBall 0 ε) := by
  classical
  intro ε hε
  let A := (Λ : ℝ) * C
  let b := K * Λ * C
  have hA : 0 ≤ A := mul_nonneg Λ.coe_nonneg hC
  have hb : 0 ≤ b := by dsimp [b] <;> positivity
  let δ := ε / (4 * (b + 1))
  let η := ε / 4
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hcoef : b * δ + η ≤ ε / 2 := by
    have h : b * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (b + 1))).mpr
      nlinarith
    dsimp [η]
    linarith
  obtain ⟨r₀, hr₀, hgood⟩ := hlower δ hδ η hη
  let F := 3 + (A + 1) * (3 * A + 2)
  have hF : 0 < F := by dsimp [F] <;> positivity
  apply exponent_le_of_separated_mass_bounds ha hafin
    (show 0 < D * F ^ k by positivity) hQ (2 * k)
  filter_upwards [eventually_ge_atTop r₀,
    eventually_logarithmic_error_le (2 * b) (2 * K) (half_pos hε)] with r hr hlog
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hrpos : 0 < r := by linarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  obtain ⟨f, s, hsep, hlow, hpaths⟩ := hgood r hr
  let t := s.image f.val.1
  have hcard : t.card = s.card := normalizedPair_card_image f hΛ s hsep
  have hsep' : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ dist x y :=
    normalizedPair_image_separated f hΛ s hsep
  let L := A * r
  let κ := A * (1 + Real.log (2 + r))
  let B := (b * δ + η) * r + b * (1 + Real.log (2 + r))
  have hL : 0 ≤ L := mul_nonneg hA hrpos.le
  have hκ : 0 ≤ κ := mul_nonneg hA hlog0
  have herr : K * (κ + 2) + B ≤ r * ε := by
    have hlin := mul_le_mul_of_nonneg_right hcoef hrpos.le
    dsimp only [κ, B, A, b] at *
    nlinarith
  have himage : ∀ x ∈ t, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
      ∀ u, ∃ z ∈ E, ‖(π (γ u)).toAdd - r • z‖ ≤ B := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨γ, hγ, hh⟩ := hpaths g hg
    obtain ⟨ζ, hζ, hmetric⟩ := normalizedPair_map_path f γ hγ
    refine ⟨ζ, ?_, ?_⟩
    · convert hmetric using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [L, κ, A] <;> ring)
    · intro u
      rw [hζ]
      exact hh u
  have hcount := hupper hrpos hL hκ hε.le herr t hsep' himage
  refine ⟨s.card, hlow, ?_⟩
  rw [← hcard]
  apply hcount.trans
  have hpoly := coarse_path_word_prefactor_le hA hr1
  dsimp only [L, κ] at *
  calc
    _ ≤ D * (F * (1 + r) ^ 2) ^ k * Real.exp (r * P (E + closedBall 0 ε)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) hpoly k
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SubgroupPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packing on the identity slice of a closed subgroup

For segment comparison the source pivot is the identity. Haar invariance
under left translations alone bounds every pulled-back ambient ball.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N G : Type} [Group N] [Group G]
  [MeasurableSpace N] [MeasurableMul N] [TopologicalSpace N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  (ι : N →* G) (μ : Measure N) [μ.IsMulLeftInvariant]

omit [TopologicalSpace N] [IsTopologicalGroup G] in
/-- Left invariance controls all ambient balls on the identity subgroup slice. -/
theorem subgroup_ball_measure (v : N) (r : ℝ) :
    μ (ι ⁻¹' closedBall (ι v) r) = μ (ι ⁻¹' closedBall (1 : G) r) := by
  let κ : PUnit.{1} →* G := 1
  let φ : PUnit.{1} →* MulAut N := 1
  have hp (d : PUnit.{1}) : MeasurePreserving (φ d) μ μ := by
    exact MeasurePreserving.id μ
  have hc (d : PUnit.{1}) (n : N) : ι (φ d n) = κ d * ι n * (κ d)⁻¹ := by
    simp [φ, κ]
  simpa only [κ, MonoidHom.one_apply, one_mul, mul_one] using
    fixedSlice_ball_measure ι κ φ μ hp hc (1 : G) PUnit.unit v r

omit [IsTopologicalGroup G] in
/-- Every relatively compact subgroup endpoint set has a separated net
with a cardinality lower bound in terms of its Haar mass. -/
theorem exists_subgroup_separated_net (hι : Continuous ι) {K S : Set N}
    (hK : IsCompact K) (hS : S ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ ι '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_separated_image_net_volume_bound μ ι
    ((hK.image hι).totallyBounded.subset (image_mono hS)) hr
  rintro x ⟨v, _, rfl⟩
  exact (subgroup_ball_measure ι μ v r).le

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanCoordinatePacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated counts for arbitrary good coordinate subsets

The coordinate Haar measure and the closed root-factor embedding give a
single finite packing constant. Every subset of a bounded rescaled chart
has its determinant volume bounded by the cardinality of an actual
ambient separated net. The subset need not itself be measurable.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
include T in
/-- A uniform ambient separated count for any bounded coordinate subset
in an actual rescaled word basis. -/
theorem exists_coordinate_subset_packing
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (cost : M.wordList → ℝ) (β : M.Bases) (r R : ℝ)
      (S : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)), S ⊆ closedBall 0 R →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => cost (β.val j)) r
      ∃ t : Finset G,
        (↑t : Set G) ⊆ (fun y => F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y)))) '' S ∧
        (∀ x ∈ t, ∀ y ∈ t, x ≠ y → ρ < dist x y) ∧
        ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume S ≤
            (t.card : ℝ≥0∞) * C := by
  classical
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let _ : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  obtain ⟨⟨chart, hc⟩, hhaar⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  have heq : ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) =
      F.ExpN ∘ (b₀.map F.N.equiv.toLinearEquiv).equivFun.symm := by
    funext y
    rw [Basis.map_equivFun]
    rfl
  have hμ : μ.IsHaarMeasure := by
    dsimp only [μ]
    rw [heq]
    exact hhaar _ (b₀.map F.N.equiv.toLinearEquiv)
  let : μ.IsHaarMeasure := hμ
  refine ⟨μ (F.inclusionN ⁻¹' closedBall (1 : G) ρ),
    fixedSlice_packing_constant_lt_top F.inclusionN μ F.closedN ρ, ?_⟩
  intro cost β r R S hS b
  let f := (F.ExpN ∘ F.N.equiv) ∘ b.equivFun.symm
  let c : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (b.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext y
    dsimp only [f, c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hc, Basis.map_equivFun]
    rfl
  have hcompact : IsCompact (f '' closedBall 0 R) :=
    (isCompact_closedBall _ _).image (hf ▸ c.continuous)
  obtain ⟨t, ht, hsep, hmass⟩ := exists_subgroup_separated_net F.inclusionN μ F.closedN.continuous
    hcompact (image_mono hS) hρ
  refine ⟨t, ?_, hsep, ?_⟩
  · simpa only [← image_comp, Function.comp_def, f] using ht
  · rw [exponential_rescaled_subset_measure F.N.equiv F.ExpN chart hc M.letter M.wordList
      b₀ β cost r S] at hmass
    exact hmass

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanInverseSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous inverse schemes in actual Cartan boxes

The same published exponential and Dynkin inputs now supply a uniformly
bounded continuous endpoint coding on a fixed ball in every actual
rescaled Cartan root-ideal chart.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
/-- Common continuous endpoint coding for all actual Cartan rescalings. -/
theorem exists_uniform_cartan_inverse_sections
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.Bases),
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
          (fun w => bracketWordExponent s w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent s (β.val j)) r
        ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
          (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
          (σ : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
            Fin (finrank ℝ (cartanRootIdeal H)) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i)
              (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i (σ y)) =
                F.ExpN (F.N.equiv (b.equivFun.symm y)) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective (F.ExpN ∘ F.N.equiv) :=
    (funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinN F.N.equiv F.ExpN
    F.isExpN M.bound_zero 2
  apply exists_uniform_rescaled_inverse_sections M.letter M.bound_zero
    M.letter_mem_wordList b₀ (F.ExpN ∘ F.N.equiv) hbij.injective
    (by simp [F.isExpN.map_zero]) (fun v => by simp [F.isExpN.map_neg])
    (fun v s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) s t)
    coeff (fun x y => ?_) (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun v => ?_)
  · simpa [List.ofFn_succ] using (hprod ![x, y]).symm
  · change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = _
    rw [F.compatibleN, hExp]
    rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentWordPath
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specified segment paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed segment visits. This retains both measurable samples and the
uniform metric bounds needed for endpoint integration.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
/-- Fixed-time samples remain continuous when the amplitudes of a fixed
combinatorial word vary continuously. -/
theorem continuous_segmentWordPath_sample
    {Y : Type} [TopologicalSpace Y]
    (v : H) (r : ℝ) (w : List (Fin M.letterCount × (Y → ℝ)))
    (hw : ∀ z ∈ w, Continuous z.2) (t : unitInterval) :
    Continuous (fun y => M.segmentWordPath T hExp realize v r
      (w.map (fun z => (z.1, z.2 y))) t) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  let w' := w.map (fun z => (z.1, fun y => z.2 y * Real.exp (r * M.segmentSupportExponent v z.1)))
  have hw' : ∀ z ∈ w', Continuous z.2 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact (hw q hq).mul_const _
  have hh := continuous_supportWordPath_sample d f hd hf hd₀ hf₀ 1 r w' hw'
    (fun _ : Y => (1 : G)) continuous_const t
  change Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
    (M.segmentScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t)
  have he : (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
      (M.segmentScaledWord v r (w.map (fun z => (z.1, z.2 y)))) 1 t) =
      (fun y => supportWordPath d f hd hf hd₀ hf₀ 1 r
        (w'.map (fun z => (z.1, z.2 y))) 1 t) := by
    funext y
    apply congrArg (fun u => supportWordPath d f hd hf hd₀ hf₀ 1 r u 1 t)
    simp only [segmentScaledWord, w', List.map_map, Function.comp_def]
  rw [he]
  exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentCoding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous endpoint families in actual segment boxes

A common coordinate ball parametrizes true endpoints in every maximizing
rescaled box. The chosen support paths have continuous time samples and
uniform bounds, so coordinates can be sampled independently of normalized
quasi-isometry pairs.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
/-- Actual segment-box endpoints have continuously sampled paths on a
common positive-radius coordinate ball, with uniform coarse metric bounds. -/
theorem exists_continuous_segment_box_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : H) :
    ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.segmentSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.segmentSupportExponent v) (β.val j)) r
      ∃ γ : ∀ y : ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
          Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))),
        (∀ t, Continuous (fun y => γ y t)) ∧
        (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
        ∀ y t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd, (l (γ y t)).toAdd = r • z := by
  classical
  obtain ⟨ε, N, B, hε, hB, hcode⟩ :=
    M.exists_uniform_cartan_inverse_sections T F hExp realize haarN dynkinN b₀
  obtain ⟨C, hC, hpath⟩ := M.exists_segmentWordPath_bound T hExp realize l hl hL hbound
    v (by linarith : 0 ≤ B) N
  refine ⟨ε, C, hε, hC, ?_⟩
  intro r hr β hβ b
  obtain ⟨w, i, σ, hσ, hs⟩ := hcode (M.segmentSupportExponent v) β hβ r hr
  let Y := ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε
  let σ' : Y → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ := fun y => σ y.val
  have hσ' : Continuous σ' := continuousOn_iff_continuous_domRestrict.mp hσ
  let u (y : Y) := generatorSchemeWord w i (σ' y)
  have hspec (y : Y) := hs y.val y.property
  have hword (z : List (Fin M.letterCount × ℝ)) :
      ((M.segmentScaledWord v r z).map
        (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod =
      F.inclusionN (generatorGroupWord
        (fun j => Real.exp (r * M.segmentSupportExponent v j) • M.letter j)
        (F.ExpN ∘ F.N.equiv) z) := by
    simp only [segmentScaledWord, List.map_map, generatorGroupWord, map_list_prod]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q _
    dsimp only [Function.comp_apply]
    rw [F.compatibleN]
    simp only [SetLike.val_smul, smul_smul]
  have hend (y : Y) :
      F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val))) =
      ((M.segmentScaledWord v r (u y)).map
        (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
    exact ((hword (u y)).trans (congrArg F.inclusionN (hspec y).2.2.2)).symm
  let γ (y : Y) := (M.segmentWordPath T hExp realize v r (u y)).cast rfl (hend y)
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro t
    have hc := M.continuous_segmentWordPath_sample T hExp realize v r
      (parameterGeneratorSchemeWord w i σ')
      (parameterGeneratorSchemeWord_continuous w i σ' hσ') t
    have he : (fun y : Y => M.segmentWordPath T hExp realize v r
        ((parameterGeneratorSchemeWord w i σ').map (fun z => (z.1, z.2 y))) t) =
        (fun y : Y => M.segmentWordPath T hExp realize v r (u y) t) := by
      funext y
      exact congrArg (fun z => M.segmentWordPath T hExp realize v r z t)
        (parameterGeneratorSchemeWord_eval w i σ' y)
    rw [he] at hc
    exact hc
  · intro y
    exact ((hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).1).cast rfl (hend y)
  · intro y t
    exact (hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).2 t

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentExponent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact source exponent of Cartan segment boxes -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (e : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The exponents of the actual segment construction equal the canonical
height-segment support exponents. -/
theorem boxCost_segment (v : H) :
    M.boxCost T hunimod e (segment ℝ 0 (e (heightProjection T.character v))) =
      fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w := by
  funext w
  unfold boxCost
  congr 1
  funext i
  rw [SupportDatum.weightSupport_segment]
  simp only [supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
    LinearEquiv.symm_apply_apply, cartanHeightWeight_projection, segmentSupportExponent]

set_option maxHeartbeats 1000000 in
/-- A maximizing segment box has precisely the support-profile exponent. -/
theorem maximizing_segment_exponent
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : H) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val) :
    columnBasisWeight
      (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val =
      (M.supportIn T hunimod e).segmentSupport (e (heightProjection T.character v)) := by
  rw [← M.boxCost_segment T hunimod e v] at hβ ⊢
  rw [M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod e b₀ _ β hβ,
    SupportDatum.templateSupport_segment]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryPaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stationary good paths to actual rescaled endpoints

Independent normalized coordinate volume and continuous endpoint coding
instantiate the stationary sampling theorem. A single normalized pair is
therefore good on an endpoint subset retaining half the coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
/-- For all large scales, one actual pair has controlled image paths to a
subset of the actual rescaled endpoints with half the coordinate volume. -/
theorem exists_stationary_good_segment_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : H) :
    ∃ (ε C : ℝ) (β : M.Bases), 0 < ε ∧ 0 ≤ C ∧
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.segmentSupportExponent v) w) β.val ∧
      ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.segmentSupportExponent v) (β.val j)) r
      ∃ (p : NormalizedPair G Λ)
        (B : Set (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε)),
        MeasurableSet B ∧
        volume (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε) * (1 / 2) ≤
          volume (Subtype.val '' Bᶜ) ∧
        ∀ y ∉ B, ∃ γ : Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))),
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
            ‖pairHeight π (γ t) p - r • z‖ ≤
              (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  obtain ⟨ε, C, hε, hC, hcode⟩ := M.exists_continuous_segment_box_paths T F hExp realize
    haarN dynkinN l hl hL hbound b₀ v
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (fun w => bracketWordExponent (M.segmentSupportExponent v) w)
  refine ⟨ε, C, β, hε, hC, hβ, ?_⟩
  apply coordinate_stationary_paths hε hC hK μ π l hπ hl hLip hsub
    (segment ℝ (0 : W) (l (Exp v)).toAdd)
    (fun r y => F.inclusionN (F.ExpN (F.N.equiv
      ((exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.segmentSupportExponent v) (β.val j)) r).equivFun.symm y.val))))
  intro r hr
  exact hcode r hr β hβ

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryPacking
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stationary good paths to actual rescaled endpoints

Independent normalized coordinate volume and continuous endpoint coding
instantiate the stationary sampling theorem. A single normalized pair is
therefore good on an exponentially large ambient separated endpoint set.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
/-- Actual separated endpoints with controlled image paths and the exact exponential lower rate. -/
theorem exists_stationary_segment_separated_set
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : H)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (ε C : ℝ) (Q : ℝ≥0∞) (β : M.Bases), 0 < ε ∧ 0 ≤ C ∧ Q < ⊤ ∧
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val ∧
      ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (t : Finset G),
        (∀ x ∈ t, ∀ y ∈ t, x ≠ y → ρ < dist x y) ∧
        ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val)) *
          volume (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε) * (1 / 2) ≤
            (t.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ t, ∃ γ : Path (1 : G) g,
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ u, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
            ‖pairHeight π (γ u) p - r • z‖ ≤
              (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  obtain ⟨ε, C, β, hε, hC, hβ, hpaths⟩ := M.exists_stationary_good_segment_paths T F
    hExp realize haarN dynkinN μ π l hπ hl hK hL hLip hbound hsub b₀ v
  obtain ⟨Q, hQ, hpack⟩ := M.exists_coordinate_subset_packing T F haarN b₀ hρ
  refine ⟨ε, C, Q, β, hε, hC, hQ, hβ, ?_⟩
  intro δ hδ η hη
  obtain ⟨r₀, hr₀, hgood⟩ := hpaths δ hδ η hη
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨p, B, hB, hvolume, hcontrol⟩ := hgood r hr
  let S := Subtype.val '' Bᶜ
  have hS : S ⊆ closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε := by
    rintro y ⟨z, _, rfl⟩
    exact ball_subset_closedBall z.property
  obtain ⟨t, ht, hsep, hcount⟩ := hpack
    (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β r ε S hS
  refine ⟨p, t, hsep, ?_, ?_⟩
  · calc
      _ = (ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val))) *
          (volume (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε) * (1 / 2)) := by ac_rfl
      _ ≤ _ := mul_le_mul' le_rfl hvolume
      _ ≤ _ := hcount
  · intro g hg
    obtain ⟨y, hy, he⟩ := ht hg
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨γ, hγ, hh⟩ := hcontrol z hz
    exact ⟨γ.cast rfl he.symm, hγ.cast rfl he.symm, hh⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual stationary segment-volume comparison

The lower count uses independently sampled coordinates of the actual root
factor. The upper count uses the image paths in the ambient group. No
volume-comparison statement is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
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
include hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The stationary mean cannot decrease the segment-support norm on the
actual Cartan algebra. This is the geometric input to kernel factorization. -/
theorem segmentSupport_le_of_stationary_mean_m_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
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
    (v : H) :
    (M.supportIn T hunimod eW).segmentSupport (π (Exp v)).toAdd ≤
      (M.supportIn T hunimod eW).segmentSupport (l (Exp v)).toAdd := by
  classical
  obtain ⟨ε₀, C, Q, β, hε₀, hC, hQ, hβ, hlow⟩ :=
    M.exists_stationary_segment_separated_set T F hExp realize haarN dynkinN
      μ π l hπ hl hK hL hLip hbound hsub b₀ v (ρ := (Λ : ℝ) * ((Λ : ℝ) + 1))
      (mul_pos hΛ (by linarith))
  let d := |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det|
  let V := Fin (finrank ℝ (cartanRootIdeal H)) → ℝ
  let a : ℝ≥0∞ := ENNReal.ofReal d * volume (ball (0 : V) ε₀) * (1 / 2)
  have hd : 0 < d := abs_pos.mpr (wordBasis_det_ne_zero M.letter M.wordList b₀ β)
  have hvol : 0 < volume (ball (0 : V) ε₀) := measure_ball_pos volume _ hε₀
  have hvolfin : volume (ball (0 : V) ε₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : V) ε₀).measure_lt_top
  have ha : 0 < a := pos_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hd).ne' hvol.ne') (by norm_num))
  have hafin : a < ⊤ := by
    dsimp [a]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolfin) (by norm_num)
  obtain ⟨D, k, hD, hupper⟩ := M.exists_coarse_path_polynomial_packing T F hunimod eW
    π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD b₀ β
    (show (0 : ℝ) < 1 by norm_num) hφ hpath hK hLip
  have hexp := M.maximizing_segment_exponent T hunimod eW b₀ v β hβ
  rw [← hπExp] at hexp
  have hE : IsCompact (segment ℝ (0 : W) (l (Exp v)).toAdd) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hne : (segment ℝ (0 : W) (l (Exp v)).toAdd).Nonempty :=
    ⟨0, left_mem_segment ℝ _ _⟩
  apply le_of_eq_of_le hexp.symm
  rw [← SupportDatum.templateSupport_segment]
  apply (M.supportIn T hunimod eW).le_templateSupport_of_thickenings
    hE hne
  apply exponent_le_of_stationary_path_counts π _ _ hΛ hK hC ha hafin hQ hD k
  · intro δ hδ η hη
    obtain ⟨r₀, hr₀, hh⟩ := hlow δ hδ η hη
    refine ⟨r₀, hr₀, ?_⟩
    intro r hr
    obtain ⟨f, s, hsep, hmass, hpaths⟩ := hh r hr
    refine ⟨f, s, hsep, ?_, hpaths⟩
    convert hmass using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [a, d, V]; ac_rfl)
  · exact hupper hE hne

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean_m_oai := @OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean_m_oai
