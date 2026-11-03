-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:10:20.088861+00:00
-- url     : https://prove2.me/submissions/f3fbb7e2-b357-4e82-9790-2ae71aa9b3b6

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D014
import Definitions.Def_OAIQ093D015
import Definitions.Def_OAIQ093D016
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_identical_neighbor_profiles

section
-- module Solutions.OAIQ093_PR.Compat
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type} {π : ι → Type} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type} [Group G]

variable (X : I → L) (Exp : L → G)

attribute [local instance] OAI.PolycyclicRecognition.boundedSchemeNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.boundedSchemeNormedSpace
/-- The one-parameter identity identifies integer multiples with group powers. -/
theorem exp_nat_smul (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : L) (k : ℕ) : Exp ((k : ℝ) • v) = (Exp v) ^ k := by
  induction k with
  | zero => simp [hzero]
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, hadd, ih, one_smul, pow_succ]

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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

namespace PolynomialCoordinateGroup

variable (m : V → V → V) (h : PolynomialGroupLaws m)

theorem exp_add_smul (x : V) (s t : ℝ) :
    exp m h ((s + t) • x) = exp m h (s • x) * exp m h (t • x) :=
  (h.2.2.2.2 x s t).symm

end PolynomialCoordinateGroup

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

/-- A fixed source ball covers a common target ball for all parameters in
one open neighborhood of the given parameter. -/
theorem exists_uniform_local_image (f : P × E → F) (p : P)
    (hf : ContDiffAt ℝ 1 f (p, 0)) (hz : f (p, 0) = 0)
    (hsurj : Function.Surjective (fun v : E => fderiv ℝ f (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ U, ball (0 : F) ε ⊆ (fun x : E => f (q, x)) '' ball 0 R := by
  let H : P × E → P × F := fun z => (z.1, f z)
  have hH : ContDiffAt ℝ 1 H (p, 0) := contDiffAt_fst.prodMk hf
  have hderiv : fderiv ℝ H (p, 0) =
      (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ f (p, 0)) := by
    exact ((hasFDerivAt_fst (p := (p, (0 : E)))).prodMk
      (hf.differentiableAt one_ne_zero).hasFDerivAt).fderiv
  have hmap := (hH.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (by
      rw [hderiv]
      exact LinearMap.range_eq_top.mpr (parameter_joint_derivative_surjective _ hsurj))
  have hvalue : H (p, 0) = (p, 0) := by simp [H, hz]
  rw [hvalue] at hmap
  have hsource : (univ : Set P) ×ˢ ball (0 : E) R ∈ 𝓝 (p, 0) :=
    prod_mem_nhds Filter.univ_mem (ball_mem_nhds _ hR)
  have himage : H '' ((univ : Set P) ×ˢ ball (0 : E) R) ∈ 𝓝 (p, (0 : F)) := by
    rw [← hmap]
    exact Filter.image_mem_map hsource
  obtain ⟨U, V, hU, hp, _hV, h0, hUV⟩ := mem_nhds_prod_iff'.mp himage
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (_hV.mem_nhds h0)
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  intro q hq y hy
  obtain ⟨⟨q', x⟩, hx, he⟩ := hUV (show (q, y) ∈ U ×ˢ V from ⟨hq, hεV hy⟩)
  have heq : q' = q := congrArg Prod.fst he
  subst q'
  exact ⟨x, hx.2, congrArg Prod.snd he⟩

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

variable {P E F J : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Pointwise submersive schemes on a compact parameter set have a common
image ball, using only finitely many of the actual schemes. -/
theorem exists_finite_uniform_submersion_family
    (f : J → P × E → F) {K : Set P} (hK : IsCompact K)
    (h : ∀ p ∈ K, ∃ j, ContDiffAt ℝ 1 (f j) (p, 0) ∧ f j (p, 0) = 0 ∧
      Function.Surjective (fun v : E => fderiv ℝ (f j) (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ (s : Finset J) (ε : ℝ), 0 < ε ∧ ∀ p ∈ K, ∃ j ∈ s,
      ball (0 : F) ε ⊆ (fun x : E => f j (p, x)) '' ball 0 R := by
  classical
  choose j hc hz hs using (fun p : K => h p.val p.property)
  choose U hU hp r hr hcover using (fun p : K =>
    exists_uniform_local_image (f (j p)) p.val (hc p) (hz p) (hs p) hR)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (by
    intro p hpK
    exact mem_iUnion.mpr ⟨⟨p, hpK⟩, hp ⟨p, hpK⟩⟩)
  obtain ⟨ε, hε, hεr⟩ := finite_positive_lower_bound s r (fun p _ => hr p)
  refine ⟨s.image j, ε, hε, ?_⟩
  intro p hpK
  obtain ⟨q, hq, hpU⟩ := mem_iUnion₂.mp (hs hpK)
  refine ⟨j q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
  exact (ball_subset_ball (hεr q hq)).trans (hcover q p hpU)

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

/-- Compactness gives finitely many schemes and one common
logarithmic image ball throughout the normalized exponential family. -/
theorem exists_uniform_coordinate_schemes {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I) (C : ℝ) :
    ∃ (schemes : Finset ((Fin (finrank ℝ V) → List (I × ℝ)) ×
        (Fin (finrank ℝ V) → I))) (ε : ℝ), 0 < ε ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C,
        ∃ s ∈ schemes, ball (0 : V) ε ⊆
          (polynomialEndpointScheme a s.1 s.2 p) '' ball 0 1 := by
  let f := fun s : (Fin (finrank ℝ V) → List (I × ℝ)) × (Fin (finrank ℝ V) → I) =>
    fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin (finrank ℝ V) → ℝ) =>
      polynomialEndpointScheme a s.1 s.2 z.1 z.2
  apply exists_finite_uniform_submersion_family f
    (isCompact_normalizedExponentialParameters a w₀ b₀ C) _ zero_lt_one
  intro p hp
  rcases hp with ⟨⟨⟨_, _, hB, hw⟩, hg⟩, hc⟩
  obtain ⟨w, i, hz, hs⟩ := exists_coordinate_submersive_scheme a p.1 hB hg hc p.2 b₀ w₀ hw
  exact ⟨(w, i), (contDiff_polynomialEndpointScheme (V := V) (k := 1) a w i).contDiffAt, hz, hs⟩

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
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

/-- The fixed finite Dynkin product retains its exact group and straight-line
one-parameter identities in the limiting coordinate law. -/
theorem gradedCoordinateBracket_groupLaws
    {G : Type} [Group G] {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    PolynomialGroupLaws (dynkinProduct a (gradedCoordinateBracket b cost)) :=
  (isClosed_dynkinGroupLaws a).mem_of_tendsto (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall (fun r =>
      basis_polynomialGroupLaws (exponentialRescaleBasis b cost r) Exp hinj hzero hneg hadd a hm))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealParameterEquicontinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single modulus for all nonnegative chart scales -/

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Joint continuity controls a compact initial interval of scales; the
joint limit at infinity controls the remaining scales. -/
theorem uniform_nonnegative_parameter_of_joint_limit
    {X : Type} [TopologicalSpace X] (E : ℝ → X → ℝ) (x₀ : X)
    (hE : Continuous (fun p : ℝ × X => E p.1 p.2))
    (hzero : ∀ r, E r x₀ = 0)
    (htail : Tendsto (fun p : ℝ × X => E p.1 p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝 x₀, ∀ r, 0 ≤ r → E r x < ε := by
  intro ε hε
  obtain ⟨s, hs, U, hU, htailU⟩ :=
    mem_prod_iff.mp (htail.eventually (gt_mem_nhds hε))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hs
  have hhead : {p : ℝ × X | E p.1 p.2 < ε} ∈
      (𝓝ˢ (Icc (0 : ℝ) (max R 0))) ×ˢ 𝓝 x₀ := by
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max R 0))).mem_nhdsSet_prod_of_forall
    intro r _
    have hh := (hE.tendsto (r, x₀)).eventually
      (gt_mem_nhds (show E r x₀ < ε by rw [hzero]; exact hε))
    change {p : ℝ × X | E p.1 p.2 < ε} ∈ 𝓝 (r, x₀) at hh
    rwa [nhds_prod_eq] at hh
  obtain ⟨V, hV, U', hU', hheadU⟩ := mem_prod_iff.mp hhead
  have hKV : Icc (0 : ℝ) (max R 0) ⊆ V := subset_of_mem_nhdsSet hV
  filter_upwards [hU, hU'] with x hx hx'
  intro r hr
  by_cases h : r ≤ max R 0
  · exact hheadU (show (r, x) ∈ V ×ˢ U' from ⟨hKV ⟨hr, h⟩, hx'⟩)
  · exact htailU (show (r, x) ∈ s ×ˢ U from
      ⟨hR r ((le_max_left _ _).trans (le_of_not_ge h)), hx⟩)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniformCoordinateGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounded generation throughout the compact law family

A common local image ball and a finite set of schemes give common length
and amplitude bounds on every fixed logarithmic ball. The scaling step uses
only the exact straight-line one-parameter identity of each coordinate group.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric
open scoped BigOperators

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

/-- A fixed bounded coordinate ball is reached by generator words with
bounds independent of the law in the compact normalized family. -/
theorem exists_uniform_bounded_coordinate_words {J : Type} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (C₀ R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C₀,
        ∀ v : V, ‖v‖ ≤ R → ∃ u : List (I × ℝ),
          u.length ≤ N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧
            polynomialWord (dynkinProduct a p.1) p.2 u = v := by
  classical
  obtain ⟨schemes, ε, hε, hcover⟩ := exists_uniform_coordinate_schemes a b₀ w₀ C₀
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
  let L : ℕ := ∑ s ∈ schemes, ∑ j, (2 * (s.1 j).length + 1)
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / ε) 0)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : R < (k : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hk)
  refine ⟨k * L, C, hC, ?_⟩
  intro p hp v hv
  obtain ⟨s, hs, hlocal⟩ := hcover p hp
  rcases hp with ⟨⟨⟨_, _, hB, _⟩, hg⟩, _⟩
  let := lieRingOfBilinear p.1 hB
  let := lieAlgebraOfBilinear p.1 hB
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a p.1) hg
  have hsmall : ‖((k : ℝ)⁻¹) • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), ← div_eq_inv_mul]
    exact (div_lt_iff₀ hk0).mpr (by simpa only [mul_comm] using lt_of_le_of_lt hv hkR)
  obtain ⟨t, ht, he⟩ := hlocal (by simpa using hsmall)
  have ht' : ‖t‖ ≤ 1 := (by simpa using ht : ‖t‖ < 1).le
  let u := generatorSchemeWord s.1 s.2 t
  have hu : generatorGroupWord p.2 Exp u = Exp (((k : ℝ)⁻¹) • v) := by
    rw [← exp_polynomialEndpointScheme a p.1 hB hg p.2 s.1 s.2 t, he]
  refine ⟨(List.replicate k u).flatten, ?_, ?_, ?_⟩
  · have hlen : u.length ≤ L := by
      rw [length_generatorSchemeWord]
      dsimp only [L]
      exact Finset.single_le_sum
        (f := fun q => ∑ j, (2 * (q.1 j).length + 1)) (fun _ _ => Nat.zero_le _) hs
    simpa only [List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul] using Nat.mul_le_mul_left k hlen
  · intro z hz
    obtain ⟨u', hu', hz⟩ := List.mem_flatten.mp hz
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hu'
    exact (generatorSchemeWord_amplitude_bound s.1 s.2 (hA s).1 (hA s).2 t ht' z hz).trans
      (hAC s hs)
  · apply Exp.injective
    rw [exp_polynomialWord]
    have hrep : generatorGroupWord p.2 Exp ((List.replicate k u).flatten) =
        (generatorGroupWord p.2 Exp u) ^ k := by
      simp only [generatorGroupWord, List.map_flatten, List.map_replicate,
        List.prod_flatten, List.prod_replicate]
    rw [hrep, hu, ← exp_nat_smul Exp (PolynomialCoordinateGroup.exp_zero _ _)
      (PolynomialCoordinateGroup.exp_add_smul _ _)]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledUniformGeneration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

variable [FiniteDimensional ℝ L] [Fintype I] [DecidableEq I]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual rescaled boxes have generator-word bounds uniform over all
exponents, nonnegative scales, and maximizing word bases. -/
theorem exists_uniform_rescaled_generator_words (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ R →
      ∃ u : List (I × ℝ), u.length ≤ N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧
        generatorGroupWord (fun i => Real.exp (r * s i) • X i) Exp u = Exp v := by
  classical
  obtain ⟨C₀, _, hc⟩ := exists_rescaledExponentialData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  let S := boundedBracketWords (I := I) k
  let bstd := Pi.basisFun ℝ (Fin (finrank ℝ L))
  have hf (β : WordBasisSelections X S) := exists_uniform_bounded_coordinate_words
    a bstd (fun j => (β.val j : FreeMagma I)) C₀ R
  choose N C hC hword using hf
  let N' := ∑ β : WordBasisSelections X S, N β
  let C' := 1 + ∑ β : WordBasisSelections X S, C β
  have hCnonneg β : 0 ≤ C β := (by norm_num : (0 : ℝ) ≤ 1).trans (hC β)
  have hC' : 1 ≤ C' := by
    dsimp [C']
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun β _ => hCnonneg β))
  refine ⟨N', C', hC', ?_⟩
  intro s β hβ r hr v hv
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  have hp : rescaledLieData X S β s r ∈
      normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I)) bstd C₀ := by
    have hbstd : (bstd : Fin (finrank ℝ L) → (Fin (finrank ℝ L) → ℝ)) =
        fun j => Pi.single j 1 := by
      funext j
      exact Pi.basisFun_apply ℝ _ j
    rw [hbstd]
    exact hc s β hβ r hr
  obtain ⟨u, hu, hCu, he⟩ := hword β _ hp (b.equivFun v) hv
  refine ⟨u, hu.trans ?_, ?_, ?_⟩
  · exact Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ β)
  · intro z hz
    have hb : C β ≤ C' := by
      have hs : C β ≤ ∑ γ : WordBasisSelections X S, C γ :=
        Finset.single_le_sum (fun γ _ => hCnonneg γ) (Finset.mem_univ β)
      dsimp [C']
      linarith
    exact (hCu z hz).trans hb
  · have hw := basis_polynomialWord b Exp hzero a hm
      (fun i => Real.exp (r * s i) • X i) u
    change Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (rescaledLieData X S β s r).1)
      (rescaledLieData X S β s r).2 u)) = _ at hw
    rw [he, LinearEquiv.symm_apply_apply] at hw
    exact hw.symm

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentWordMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric bounds for the actual unit-weight nilpotent charts -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A word of bounded length and bounded letters has the corresponding
metric bound in every group with a left invariant metric. -/
theorem dist_generatorGroupWord_le
    {I L G : Type} [SMul ℝ L] [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (X : I → L) (Exp : L → G) (u : List (I × ℝ)) {B D : ℝ}
    (hu : ∀ z ∈ u, |z.2| ≤ B)
    (hstep : ∀ i t, |t| ≤ B → dist 1 (Exp (t • X i)) ≤ D) :
    dist 1 (generatorGroupWord X Exp u) ≤ (u.length : ℝ) * D := by
  induction u with
  | nil => simp [generatorGroupWord]
  | cons z u ih =>
    rw [generatorGroupWord_cons]
    have hz := hstep z.1 z.2 (hu z (by simp))
    have hr := ih (fun w hw => hu w (by simp [hw]))
    calc
      _ ≤ dist 1 (Exp (z.2 • X z.1)) +
          dist (Exp (z.2 • X z.1)) (Exp (z.2 • X z.1) * generatorGroupWord X Exp u) :=
        dist_triangle _ _ _
      _ = dist 1 (Exp (z.2 • X z.1)) + dist 1 (generatorGroupWord X Exp u) := by
        congr 1
        simpa only [mul_one] using
          dist_mul_left (Exp (z.2 • X z.1)) 1 (generatorGroupWord X Exp u)
      _ ≤ D + (u.length : ℝ) * D := add_le_add hz hr
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] <;> ring

/-- Uniform generator-word bounds imply linear metric growth on every
fixed-radius unit-weight chart. Only continuity of the generating flows
is required from the metric; no geodesic or scaling estimate is assumed. -/
theorem exists_unit_weight_chart_metric_bound
    {I L G : Type} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X : I → L) {k c : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hcont : ∀ i, Continuous (fun t : ℝ => Exp (t • X i)))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent (fun _ : I => 1) w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent (fun _ : I => 1) (β.val i)) r).equivFun v‖ ≤ R →
      dist 1 (Exp v) ≤ C * Real.exp r := by
  classical
  obtain ⟨N, B, hB, hgen⟩ := exists_uniform_rescaled_generator_words X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch R
  choose D hD hflow using fun i => continuous_flow_coarse_bound
    (fun t : ℝ => Exp (t • X i)) (hcont i) (by simpa using hzero) (hadd (X i))
  let D₀ := ∑ i, D i
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg (fun i _ => hD i)
  have hDi (i : I) : D i ≤ D₀ :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
  refine ⟨(N : ℝ) * (D₀ * (1 + B)), by positivity, ?_⟩
  intro β hβ r hr v hv
  obtain ⟨u, hu, hub, hue⟩ := hgen (fun _ : I => 1) β hβ r hr v hv
  have her : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
  have hstep (i : I) (t : ℝ) (ht : |t| ≤ B) :
      dist 1 (Exp (t • (Real.exp (r * (1 : ℝ)) • X i))) ≤ D₀ * (1 + B) * Real.exp r := by
    rw [smul_smul, mul_one]
    calc
      _ ≤ D i * (1 + |t * Real.exp r|) := hflow i _
      _ ≤ D₀ * (1 + B * Real.exp r) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        gcongr
        exact hDi i
      _ ≤ D₀ * ((1 + B) * Real.exp r) := by
        apply mul_le_mul_of_nonneg_left _ hD₀
        nlinarith
      _ = _ := by ring
  rw [← hue]
  calc
    _ ≤ (u.length : ℝ) * (D₀ * (1 + B) * Real.exp r) :=
      dist_generatorGroupWord_le _ Exp u hub hstep
    _ ≤ (N : ℝ) * (D₀ * (1 + B) * Real.exp r) := by gcongr
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledMetricSmallness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing normalized coordinates give sublinear metric displacement -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {L J : Type} [LieRing L] [LieAlgebra ℝ L]

/-- Shifting the logarithmic scale changes each coordinate by one fixed
factor. This identity does not require the costs to be positive. -/
theorem repr_shift_exponentialRescaleBasis
    (b : Basis J ℝ L) (cost : J → ℝ) (r a : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b cost (r + a)).repr x j =
      Real.exp (-a * cost j) * (exponentialRescaleBasis b cost r).repr x j := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- All coordinates obey one common bound for a fixed shift. -/
theorem norm_shift_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (r a : ℝ) (x : L) :
    ‖(exponentialRescaleBasis b cost (r + a)).equivFun x‖ ≤
      (∑ j, Real.exp (-a * cost j)) * ‖(exponentialRescaleBasis b cost r).equivFun x‖ := by
  have hc : 0 ≤ ∑ j, Real.exp (-a * cost j) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b cost (r + a)).repr x j| ≤ _
  rw [repr_shift_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul
    (Finset.single_le_sum (f := fun i => Real.exp (-a * cost i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j))
    (norm_le_pi_norm ((exponentialRescaleBasis b cost r).equivFun x) j)
    (abs_nonneg _) hc

/-- A unit-chart metric estimate at every large scale implies that every
sequence with normalized coordinates tending to zero has sublinear length.
The proof uses a fixed smaller scale before passing to the limit. -/
theorem metric_sublinear_of_rescaled_coordinates_tendsto_zero
    {G ι : Type} [Group G] [PseudoMetricSpace G] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (Exp : L → G)
    {C : ℝ} (_hC : 0 ≤ C)
    (hmetric : ∀ s : ℝ, 0 ≤ s → ∀ x : L,
      ‖(exponentialRescaleBasis b cost s).equivFun x‖ ≤ 1 →
        dist 1 (Exp x) ≤ C * Real.exp s)
    {l : Filter ι} (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (x : ι → L)
    (hsmall : Tendsto (fun i => (exponentialRescaleBasis b cost (scale i)).equivFun (x i))
      l (𝓝 0)) :
    Tendsto (fun i => dist 1 (Exp (x i)) / Real.exp (scale i)) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun i => ha.trans_le (by positivity))
  · intro ε hε
    have hexp := Real.tendsto_exp_atBot.const_mul C
    simp only [mul_zero] at hexp
    obtain ⟨a, ha⟩ := (hexp.eventually (eventually_lt_nhds hε)).exists
    let B := ∑ j, Real.exp (-a * cost j)
    have hsmall' : Tendsto (fun i => B *
        ‖(exponentialRescaleBasis b cost (scale i)).equivFun (x i)‖) l (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using hsmall.norm.const_mul B
    filter_upwards [hscale.eventually (eventually_ge_atTop (-a)),
      hsmall'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hs
    have hcoord : ‖(exponentialRescaleBasis b cost (scale i + a)).equivFun (x i)‖ ≤ 1 :=
      (norm_shift_exponentialRescaleBasis_le b cost (scale i) a (x i)).trans hs.le
    have hm := hmetric (scale i + a) (by linarith) (x i) hcoord
    calc
      dist 1 (Exp (x i)) / Real.exp (scale i) ≤
          (C * Real.exp (scale i + a)) / Real.exp (scale i) := by gcongr
      _ = C * Real.exp a := by rw [Real.exp_add]; field_simp
      _ < ε := ha

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledChartDistances
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric convergence for pairs of rescaled chart points -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {L G : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] {n c : ℕ}

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
/-- The coordinate of a quotient of exponential-chart points is the exact
Dynkin product. This identity transfers polynomial convergence to distance. -/
theorem exp_chart_difference (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (x y : Fin n → ℝ) :
    Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) (-x) y)) =
      (Exp (b.equivFun.symm x))⁻¹ * Exp (b.equivFun.symm y) := by
  have he := basis_dynkinProduct b a (b.equivFun.symm (-x)) (b.equivFun.symm y)
  simp only [LinearEquiv.apply_symm_apply] at he
  rw [he, LinearEquiv.symm_apply_apply, hm, map_neg, hneg]

/-- If two normalized chart points approach the same point, their distance
in the original group, divided by the dilation, tends to zero. -/
theorem rescaled_chart_distance_tendsto_zero
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 →
        dist 1 (Exp v) ≤ C * Real.exp r)
    {ι : Type} {l : Filter ι} (scale : ι → ℝ) (hscale : Tendsto scale l atTop)
    (x y : ι → Fin n → ℝ) {z : Fin n → ℝ}
    (hx : Tendsto x l (𝓝 z)) (hy : Tendsto y l (𝓝 z)) :
    Tendsto (fun i =>
      dist (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))
        (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i))) /
          Real.exp (scale i)) l (𝓝 0) := by
  let B₀ := gradedCoordinateBracket b cost
  let B := fun i => basisBracket (exponentialRescaleBasis b cost (scale i))
  have hB : Tendsto B l (𝓝 B₀) := by
    simpa only [B, B₀, Function.comp_def] using
      (basisBracket_rescale_tendsto b cost hweight).comp hscale
  have hcont : Continuous (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
        ((Fin n → ℝ) × (Fin n → ℝ)) => dynkinProduct a p.1 (-p.2.1) p.2.2) :=
    continuous_dynkinProduct
      (P := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
        ((Fin n → ℝ) × (Fin n → ℝ))) a (fun p => p.1) (fun p => -p.2.1) (fun p => p.2.2)
      continuous_fst continuous_snd.fst.neg continuous_snd.snd
  have hlim := gradedCoordinateBracket_groupLaws b cost hweight Exp hinj hzero hneg hadd a hm
  have hq : Tendsto (fun i => dynkinProduct a (B i) (-x i) (y i)) l (𝓝 0) := by
    have ht := (hcont.tendsto (B₀, (z, z))).comp (hB.prodMk_nhds (hx.prodMk_nhds hy))
    simpa only [Function.comp_def, B₀, hlim.2.2.2.1 z] using ht
  let v := fun i => (exponentialRescaleBasis b cost (scale i)).equivFun.symm
    (dynkinProduct a (B i) (-x i) (y i))
  have hv : Tendsto (fun i => (exponentialRescaleBasis b cost (scale i)).equivFun (v i))
      l (𝓝 0) := by simpa only [v, LinearEquiv.apply_symm_apply] using hq
  have ht := metric_sublinear_of_rescaled_coordinates_tendsto_zero b cost Exp hC hmetric
    scale hscale v hv
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  congr 1
  rw [show Exp (v i) =
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))⁻¹ *
        Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i)) from
      exp_chart_difference _ Exp hneg a hm (x i) (y i)]
  simpa only [inv_mul_cancel] using
    (dist_mul_left
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))⁻¹
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (x i)))
      (Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm (y i)))).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AffineProfileConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration near a finite family of affine profiles -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal

/-- A closed event disjoint from the support of the limit has probability
converging to zero. -/
theorem measure_closed_tendsto_zero_of_support
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [HasOuterApproxClosed S] [HereditarilyLindelofSpace S]
    {μn : ℕ → ProbabilityMeasure S} {μ : ProbabilityMeasure S}
    (hμ : Tendsto μn atTop (𝓝 μ)) {B : Set S} (hB : IsClosed B)
    (hs : ∀ f ∈ (μ : Measure S).support, f ∉ B) :
    Tendsto (fun n => (μn n : Measure S) B) atTop (𝓝 0) := by
  have hz : (μ : Measure S) B = 0 := by
    apply measure_mono_null _ (μ : Measure S).measure_compl_support
    intro f hf
    exact fun hfs => hs f hfs hf
  apply tendsto_of_le_liminf_of_limsup_le zero_le
  simpa only [hz] using ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hB

/-- Compactness turns a statement about every supported sequential limit
into concentration for the original sequence. -/
theorem measure_closed_tendsto_zero_of_all_supported_limits
    {S : Type} [TopologicalSpace S] [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S] (μn : ℕ → ProbabilityMeasure S)
    {B : Set S} (hB : IsClosed B)
    (hs : ∀ (ι : ℕ → ℕ), StrictMono ι → ∀ μ : ProbabilityMeasure S,
      Tendsto (μn ∘ ι) atTop (𝓝 μ) → ∀ f ∈ (μ : Measure S).support, f ∉ B) :
    Tendsto (fun n => (μn n : Measure S) B) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨u, hu, hnu⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨μ, v, hv, hμ⟩ := CompactSpace.tendsto_subseq (μn ∘ ns ∘ u)
  refine ⟨u ∘ v, ?_⟩
  exact measure_closed_tendsto_zero_of_support hμ hB
    (hs (ns ∘ u ∘ v) (hnu.comp hv) μ hμ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileCompactness
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact containment for families of chart profiles -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {X W I : Type} [TopologicalSpace X] [MetricSpace W] [ProperSpace W]

/-- Equicontinuous profiles with pointwise bounded values lie in one compact
set for locally uniform convergence. The domain need not itself be compact. -/
theorem exists_compact_containing_profiles
    (F : I → C(X, W)) (hequi : Equicontinuous (fun i x => F i x))
    (w₀ : W) (hbound : ∀ x, ∃ R : ℝ, ∀ i, dist (F i x) w₀ ≤ R) :
    ∃ S : Set C(X, W), IsCompact S ∧ ∀ i, F i ∈ S := by
  let A : Set (X → W) := range (fun i x => F i x)
  have hA : A.Equicontinuous := by
    exact (equicontinuous_iff_range).mp hequi
  have hcls : (closure A).Equicontinuous := hA.closure
  have hcontinuous : ∀ f ∈ closure A, Continuous f := by
    intro f hf
    exact hcls.continuous ⟨f, hf⟩
  choose R hR using hbound
  have hsubset : A ⊆ {f : X → W | ∀ x, f x ∈ closedBall w₀ (R x)} := by
    rintro f ⟨i, rfl⟩ x
    exact hR x i
  have hclosed : IsClosed {f : X → W | ∀ x, f x ∈ closedBall w₀ (R x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_closedBall.preimage (continuous_apply x))
  have hcompact : IsCompact (closure A) :=
    (isCompact_pi_infinite (fun x => isCompact_closedBall w₀ (R x))).of_isClosed_subset
      isClosed_closure (closure_minimal hsubset hclosed)
  let S : Set C(X, W) := {f | (f : X → W) ∈ closure A}
  have himage : ContinuousMap.toFun '' S = closure A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hcontinuous f hf⟩, hf, rfl⟩
  refine ⟨S, ?_, ?_⟩
  · apply ArzelaAscoli.isCompact_of_equicontinuous S
    · rwa [himage]
    · exact hcls.comp (fun f : S => ⟨f.val, f.property⟩)
  · intro i
    exact subset_closure (mem_range_self i)

end PolycyclicRecognition

end

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

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equicontinuity of actual rescaled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

variable {G W Z : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rescaledMapProfile_dist_le {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (z w : Z) :
    dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) ≤
      (K : ℝ) * (dist (φ z) (φ w) / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k * φ z) (x * k * φ w)
  rw [dist_mul_left] at hh
  have he : dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) =
      dist (J (x * k * φ z)) (J (x * k * φ w)) / Real.exp r := by
    simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
      sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (Real.exp_pos r), div_eq_mul_inv, mul_comm]
  rw [he]
  calc
    _ ≤ ((K : ℝ) * dist (φ z) (φ w)) / Real.exp r := div_le_div_of_nonneg_right hh (Real.exp_pos r).le
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AllScaleProfileEquicontinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equicontinuity before choosing a sequence of scales -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

theorem continuous_mapped_scaled_basis_coordinates
    {L V : Type} [LieRing L] [LieAlgebra ℝ L] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {n : ℕ}
    (e : L →ₗ[ℝ] V) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) =>
      e ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)) := by
  simp only [Basis.equivFun_symm_apply, exponentialRescaleBasis, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, map_sum, map_smul]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_snd).smul
    ((Real.continuous_exp.comp (continuous_fst.mul continuous_const)).smul continuous_const)

/-- Uniformity of the actual metric error over all nonnegative real scales.
Compact initial scale intervals and the asymptotic chart estimate give a
single modulus, independent of the eventual sequence. -/
theorem equicontinuous_all_scale_profiles
    {L G W P : Type} [LieRing L] [LieAlgebra ℝ L]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n c : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 →
        dist 1 (Exp v) ≤ C * Real.exp r)
    (hchart : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      Exp ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)))
    (scale : P → ℝ) (hscale : ∀ p, 0 ≤ scale p)
    {K : ℝ≥0} (J : P → G → W) (hJ : ∀ p, LipschitzWith K (J p))
    (x k : P → G) :
    Equicontinuous (fun p => rescaledMapProfile (J p) (x p) (k p) (scale p)
      (fun z => Exp ((exponentialRescaleBasis b cost (scale p)).equivFun.symm z))) := by
  let φ := fun r z => Exp ((exponentialRescaleBasis b cost r).equivFun.symm z)
  intro z₀
  let E := fun r z => (K : ℝ) * (dist (φ r z₀) (φ r z) / Real.exp r)
  have hE : Continuous (fun p : ℝ × (Fin n → ℝ) => E p.1 p.2) :=
    continuous_const.mul
      (((hchart.comp (continuous_fst.prodMk continuous_const)).dist hchart).div
        (Real.continuous_exp.comp continuous_fst) (fun p => (Real.exp_pos p.1).ne'))
  have htail : Tendsto (fun p : ℝ × (Fin n → ℝ) => E p.1 p.2)
      (atTop ×ˢ 𝓝 z₀) (𝓝 0) := by
    have hd := rescaled_chart_distance_tendsto_zero b cost hweight Exp hinj hzero hneg
      hadd a hm hC hmetric Prod.fst tendsto_fst
      (fun _ => z₀) Prod.snd tendsto_const_nhds tendsto_snd
    simpa only [E, φ, mul_zero] using hd.const_mul (K : ℝ)
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [uniform_nonnegative_parameter_of_joint_limit E z₀ hE
    (fun r => by simp [E]) htail ε hε] with z hz
  intro p
  exact (rescaledMapProfile_dist_le (hJ p) (x p) (k p) (scale p) (φ (scale p)) z₀ z).trans_lt
    (hz (scale p) (hscale p))

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfileChainConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating a profile through a bounded number of interior switches

The individual switch theorem is applied to marginal laws. Compactness
then gives joint concentration of every intermediate profile near the
initial one. The number of switches is fixed; no simultaneous success
assumption about all probes is needed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

variable {V W : Type} [TopologicalSpace V] [LocallyCompactSpace V]
  [NormedAddCommGroup W]

omit [LocallyCompactSpace V] in
/-- Equality of all adjacent marginal limits propagates through the
whole finite chain, on the actual compact set of profile coordinates. -/
theorem profile_chain_concentration
    (S : Set C(V, W)) [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (Z : Set V) [CompactSpace Z] (n : ℕ)
    (μ : ℕ → ProbabilityMeasure (Fin (n + 1) → S))
    (hedge : ∀ i : Fin n, ∀ ι : ℕ → ℕ, StrictMono ι →
      ∀ ν : ProbabilityMeasure (S × S),
      Tendsto (fun k => ProbabilityMeasure.map (μ (ι k))
        (f := (fun f => (f i.castSucc, f i.succ))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν) →
      ∀ f ∈ (ν : Measure (S × S)).support, ∀ z ∈ Z, f.1.val z = f.2.val z)
    (j : Fin (n + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k => (μ k : Measure (Fin (n + 1) → S))
      {f | η ≤ dist ((f j).val.restrict Z) ((f 0).val.restrict Z)}) atTop (𝓝 0) := by
  have hcoord (i : Fin (n + 1)) :
      Continuous (fun f : Fin (n + 1) → S => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  apply measure_closed_tendsto_zero_of_all_supported_limits μ
    (isClosed_le continuous_const ((hcoord j).dist (hcoord 0)))
  intro ι hι ν hν f hf
  have hadj (i : Fin n) (z : V) (hz : z ∈ Z) :
      (f i.castSucc).val z = (f i.succ).val z := by
    let p : (Fin (n + 1) → S) → S × S := fun g => (g i.castSucc, g i.succ)
    have hp : Continuous p := (continuous_apply _).prodMk (continuous_apply _)
    have hmap : Tendsto (fun k => ProbabilityMeasure.map (μ (ι k)) (f := p) (by first | exact hp.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        atTop (𝓝 (ProbabilityMeasure.map ν (f := p) (by first | exact hp.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) :=
      (ProbabilityMeasure.continuous_map hp).continuousAt.tendsto.comp hν
    exact hedge i ι hι (ProbabilityMeasure.map ν (f := p) (by first | exact hp.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) hmap (p f)
      (mem_support_map_of_continuous ν p hp hf) z hz
  have hall (i : Fin (n + 1)) : ∀ z ∈ Z, (f i).val z = (f 0).val z := by
    induction i using Fin.induction with
    | zero => intro z hz; rfl
    | succ i hi =>
      intro z hz
      exact (hadj i z hz).symm.trans (hi z hz)
  have heq : (f j).val.restrict Z = (f 0).val.restrict Z := by
    ext z
    exact hall j z.val z.property
  simpa only [mem_ofPred_eq, heq, dist_self, not_le] using hη

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurableProbeProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable profiles of the Borel-selected probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {G W Z : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace Z]
  [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]

/-- A Borel suffix selector gives a Borel profile in the fixed compact
profile family, with the actual formula on the carrying sample cell. -/
theorem exists_measurable_borel_sampled_profile
    {A : Type} [MeasurableSpace A]
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) (suffix : A → G) (hsuffix : Measurable suffix)
    (C : Set A) (hC : MeasurableSet C) (hne : C.Nonempty)
    (S : Set C(Z, W))
    (hmem : ∀ a ∈ C, rescaledContinuousProfile J hJ x (suffix a) r φ hφ ∈ S) :
    ∃ profile : A → S, Measurable profile ∧ ∀ a ∈ C, ∀ z,
      (profile a).val z = rescaledMapProfile J x (suffix a) r φ z := by
  classical
  let F : C → S := fun a =>
    ⟨rescaledContinuousProfile J hJ x (suffix a.val) r φ hφ, hmem a.val a.property⟩
  have hF : Measurable F :=
    (((continuous_rescaledContinuousProfile J hJ x r φ hφ).measurable.comp hsuffix).comp
      measurable_subtype_coe).subtype_mk
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨profile, hp, heq⟩ := (MeasurableEmbedding.subtype_coe hC).exists_measurable_extend
    hF (fun _ => ⟨F ⟨a₀, ha₀⟩⟩)
  refine ⟨profile, hp, ?_⟩
  intro a ha z
  exact congrArg (fun f : S => f.val z) (congrFun heq ⟨a, ha⟩)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ProfilePointwiseBounds
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor bounds and compact containment for sampled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W Z : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Zero Z]

/-- A bound at the identity extends to a pointwise bound by the actual
scaled chart distance. -/
theorem rescaledMapProfile_norm_le
    {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : φ 0 = 1) (z : Z) :
    ‖rescaledMapProfile J x k r φ z‖ ≤
      (K : ℝ) * (dist 1 (φ z) / Real.exp r) + ‖rescaledMapProfile J x k r φ 0‖ := by
  calc
    _ = ‖(rescaledMapProfile J x k r φ z - rescaledMapProfile J x k r φ 0) +
        rescaledMapProfile J x k r φ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖rescaledMapProfile J x k r φ z - rescaledMapProfile J x k r φ 0‖ +
        ‖rescaledMapProfile J x k r φ 0‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [← dist_eq_norm]
      apply add_le_add _ (le_refl _)
      simpa only [hφ, dist_comm] using rescaledMapProfile_dist_le hJ x k r φ z 0

/-- The profile value at the identity is controlled by the suffix length. -/
theorem rescaledMapProfile_zero_norm_le
    {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : φ 0 = 1) :
    ‖rescaledMapProfile J x k r φ 0‖ ≤ (K : ℝ) * (dist 1 k / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k) x
  have he : dist (x * k) x = dist 1 k := by
    simpa only [mul_one, dist_comm] using dist_mul_left x k 1
  rw [he] at hh
  simp only [rescaledMapProfile, hφ, mul_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.exp_pos r), ← dist_eq_norm]
  calc
    _ ≤ (Real.exp r)⁻¹ * ((K : ℝ) * dist 1 k) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Real.exp_pos r).le)
    _ = _ := by ring

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

set_option maxHeartbeats 1000000 in
omit [SimplyConnectedSpace G] in
/-- Right translation of a sheet changes its deterministic suffix and
preserves the original coordinate-cube sampling law exactly. -/
theorem translated_groupBox_profile_law_mul_right
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) (k₀ k : F.N.carrier)
    {X : Type} [MeasurableSpace X] (profile : F.N.carrier → X) (hp : Measurable profile) :
    ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r k₀)
      (f := (fun q => profile (q * k))) (hp.comp (continuous_id.mul continuous_const).measurable).aemeasurable = ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r (k₀ * k))
      (f := profile) hp.aemeasurable := by
  have h₀ := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN b₀
    E β r k₀ (fun q => profile (q * k)) (hp.comp (continuous_id.mul continuous_const).measurable)
  have h₁ := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN b₀
    E β r (k₀ * k) profile hp
  dsimp only at h₀ h₁
  rw [← h₀, ← h₁]
  congr 1
  funext y
  simp only [Function.comp_apply, mul_assoc]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control of the actual Cartan factor charts -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Matrix.Norms.Operator Topology

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
include T in
/-- Bounded normalized coordinates in the Cartan factor have ambient
distance at most a constant times the dilation scale. This follows from
the actual finite generator words, not a metric-scaling hypothesis. -/
theorem exists_cartan_d_chart_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent (fun _ : I => 1) w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun i => bracketWordExponent (fun _ : I => 1) (β.val i)) r).equivFun v‖ ≤ R →
      dist 1 (F.inclusionD (F.ExpD (F.D.equiv v))) ≤ C * Real.exp r := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbij : Function.Bijective (F.ExpD ∘ F.D.equiv) :=
    (funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective
  let E : H → G := fun v => F.inclusionD (F.ExpD (F.D.equiv v))
  have hcont (i : I) : Continuous (fun t : ℝ => E (t • X i)) := by
    simpa [E, F.compatibleD] using
      continuous_exp_line_of_published_realization T ExpG hExpG realize (X i)
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD
    F.isExpD hk 2
  apply exists_unit_weight_chart_metric_bound X hk hletters b₀ E
    (F.closedD.injective.comp hbij.injective)
    (by simp [E, F.isExpD.map_zero]) (fun v => by simp [E, F.isExpD.map_neg])
    (fun v s t => by simp only [E, map_smul, F.isExpD.map_add_smul, map_mul])
    hcont coeff (fun x y => ?_) (j.comp H.incl) ρ hρ (fun v => ?_) R
  · have hh := congrArg F.inclusionD (hprod ![x, y]).symm
    simpa [E, List.ofFn_succ] using hh
  · dsimp only [E]
    rw [F.compatibleD, hmatch]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborChainConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original neighboring comparison along finite root chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  [CompactSpace Profiles] [MetrizableSpace Profiles]
  {Λ : ℝ≥0}

set_option maxHeartbeats 1000000 in
omit [SecondCountableTopology F.N.carrier] [BorelSpace (Profiles × Profiles)] in
/-- The proved neighboring-sheet comparison propagates along a bounded
root word. Its root index may change at each scale and each edge. -/
theorem neighbor_chain_concentration
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    (hneighbor : ∀ row : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
      haarN chartN hchartN pivot B δ Profiles (Λ := Λ),
      ∀ z ∈ Z, row.point.1.val z = row.point.2.val z)
    (scale : ℕ → ℝ) (hgrows : Tendsto scale atTop atTop)
    (hmono : StrictMono scale) (hs1 : ∀ n, 1 ≤ scale n)
    (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (radius : ℕ → ℝ) (hr0 : ∀ n, 0 ≤ radius n)
    (hr : HasSubexponentialUpperBoundSeq scale radius)
    {N : ℕ} (base : ℕ → Fin (N + 1) → F.N.carrier)
    (step : ℕ → Fin N → F.N.carrier)
    (hbase : ∀ n j, base n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n))
    (hstep : ∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n))
    (hnext : ∀ n j, base n j.succ = base n j.castSucc * step n j)
    (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ)
    (htime : ∀ n j, |time n j| ≤ radius n * Real.exp
      ((M.weight (mode n j) (pivot (mode n j)) + δ * B) * scale n))
    (hroot : ∀ n j, F.inclusionN (step n j) =
      Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (profile : ℕ → F.N.carrier → Profiles) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n j q, q ∈ (fun v => v * base n j) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (j : Fin (N + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN cell β (scale n) 1 : Measure F.N.carrier)
      {q | η ≤ dist ((profile n (q * base n j)).val.restrict Z)
        ((profile n (q * base n 0)).val.restrict Z)}) atTop (𝓝 0) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN cell β (scale n) 1
  let chain := fun n q (j : Fin (N + 1)) => profile n (q * base n j)
  have hc (n) : Measurable (chain n) := Measurable.of_eval (fun j =>
    (hp n).comp (measurable_id.mul_const _))
  have hedge (edge : Fin N) (ι : ℕ → ℕ) (hι : StrictMono ι)
      (ν : ProbabilityMeasure (Profiles × Profiles))
      (hν : Tendsto (fun n => ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ (ι n)) (f := (chain (ι n))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        (f := (fun f => (f edge.castSucc, f edge.succ))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 ν)) :
      ∀ f ∈ (ν : Measure (Profiles × Profiles)).support,
        ∀ z ∈ Z, f.1.val z = f.2.val z := by
    obtain ⟨i, u, hu, hmode⟩ := exists_constant_mode_subsequence (fun n => mode (ι n) edge)
    let v := ι ∘ u
    have hv : StrictMono v := hι.comp hu
    have hmarg (n) : ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ n) (f := (chain n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (f := (fun f => (f edge.castSucc, f edge.succ))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) =
        ProbabilityMeasure.map
          (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
            cell β (scale n) (base n edge.castSucc))
          (f := (fun q => (profile n q, profile n (q * step n edge)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable) := by
      have hpair : Measurable (fun q => (profile n q, profile n (q * step n edge))) :=
        (hp n).prodMk ((hp n).comp (measurable_id.mul_const _))
      have htrans := M.translated_groupBox_profile_law_mul_right T F hunimod eW
        haarN chartN hchartN bN cell β (scale n) 1 (base n edge.castSucc) _ hpair
      rw [one_mul] at htrans
      rw [← htrans]
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (hc n)]
      congr 1
      funext q
      simp only [Function.comp_apply, chain, hnext, mul_assoc]
    have hconv : Tendsto (fun n => ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
          cell β (scale (v n)) (base (v n) edge.castSucc))
        (f := (fun q => (profile (v n) q, profile (v n) (q * step (v n) edge)))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        atTop (𝓝 ν) := by
      apply (hν.comp hu.tendsto_atTop).congr'
      filter_upwards [] with n
      exact hmarg (v n)
    intro f hf z hz
    let row : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
        haarN chartN hchartN pivot B δ Profiles (Λ := Λ) := {
      scale := scale ∘ v
      grows := hgrows.comp hv.tendsto_atTop
      strict_mono := hmono.comp hv
      scale_ge_one := fun n => hs1 (v n)
      pair := pair ∘ v
      center := center ∘ v
      radius := radius ∘ v
      radius_nonneg := fun n => hr0 (v n)
      radius_subexponential := fun ε hε => hv.tendsto_atTop.eventually (hr ε hε)
      base := fun n => base (v n) edge.castSucc
      step := fun n => step (v n) edge
      base_mem := fun n => hbase (v n) edge.castSucc
      step_mem := fun n => hstep (v n) edge
      mode := i
      time := fun n => time (v n) edge
      time_bound := by
        intro n
        simpa only [v, Function.comp_apply, hmode n] using htime (v n) edge
      root_step := by
        intro n
        simpa only [v, Function.comp_apply, hmode n] using hroot (v n) edge
      profile := profile ∘ v
      measurable_profile := fun n => hp (v n)
      actual := by
        intro n q hq w
        rcases hq with hq | hq
        · exact hactual (v n) edge.castSucc q hq w
        · apply hactual (v n) edge.succ q _ w
          simpa only [hnext, mul_assoc, Function.comp_apply] using hq
      law := ν
      converges := hconv
      point := f
      supported := hf }
    exact hneighbor row z hz
  have hprob := profile_chain_concentration Profiles Z N
    (fun n => ProbabilityMeasure.map (μ n) (f := (chain n)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) hedge j hη
  apply hprob.congr'
  filter_upwards [] with n
  apply ProbabilityMeasure.map_apply' (μ n) (hc n).aemeasurable
  have hcoord (i : Fin (N + 1)) :
      Continuous (fun f : Fin (N + 1) → Profiles => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  exact (isClosed_le continuous_const ((hcoord j).dist (hcoord 0))).measurableSet

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedChainConcentration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-chain concentration from the precisely published inputs -/

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
/-- A single enlargement threshold works along every finite original root
chain. No comparison of neighboring limits is assumed in this statement. -/
theorem exists_uniform_published_chain_concentration
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
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (hProfiles : IsCompact Profiles)
    [HasOuterApproxClosed Profiles] [HasOuterApproxClosed (Profiles × Profiles)]
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
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ Z : Set (Fin (finrank ℝ H) → ℝ), ∀ _ : CompactSpace Z,
      (∀ z ∈ Z, eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
    (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n)
    (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (radius : ℕ → ℝ) (_hr0 : ∀ n, 0 ≤ radius n)
    (_hr : HasSubexponentialUpperBoundSeq scale radius)
    {N : ℕ} (base : ℕ → Fin (N + 1) → F.N.carrier)
    (step : ℕ → Fin N → F.N.carrier)
    (_hbase : ∀ n j, base n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hstep : ∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hnext : ∀ n j, base n j.succ = base n j.castSucc * step n j)
    (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ)
    (_htime : ∀ n j, |time n j| ≤ radius n * Real.exp
      ((M.weight (mode n j) (pivot (mode n j)) + δ * B) * scale n))
    (_hroot : ∀ n j, F.inclusionN (step n j) =
      Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (profile : ℕ → F.N.carrier → Profiles) (_hp : ∀ n, Measurable (profile n))
    (_hactual : ∀ n j q, q ∈ (fun v => v * base n j) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (j : Fin (N + 1)) {η : ℝ} (_hη : 0 < η),
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (scale n) 1 : Measure F.N.carrier)
      {q | η ≤ dist ((profile n (q * base n j)).val.restrict Z)
        ((profile n (q * base n 0)).val.restrict Z)}) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hident⟩ := M.exists_uniform_identical_neighbor_profiles T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber Profiles hProfiles hnz
    sourceInputs sourceDynkin targetInputs
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd Z hZ hZheight scale hgrows hmono hs1 pair center radius hr0 hr
    N base step hbase hstep hnext mode time htime hroot profile hp hactual j η hη
  let := hZ
  let : CompactSpace Profiles := isCompact_iff_compactSpace.mp hProfiles
  have hneighbor (row : NeighborSamplingRow T M F hunimod eW π bN Eall γ X βD
      haarN chartN hchartN pivot B δ Profiles (Λ := Λ)) :
      ∀ z ∈ Z, row.point.1.val z = row.point.2.val z := by
    obtain ⟨A, b, hab⟩ := hident δ hδ hd row
    intro z hz
    exact (hab z (hZheight z hz)).1.trans (hab z (hZheight z hz)).2.symm
  exact M.neighbor_chain_concentration T F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot B δ Profiles Z hneighbor scale hgrows hmono hs1
    pair center radius hr0 hr base step hbase hstep hnext mode time htime hroot
    profile hp hactual j hη

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniversalAllScaleCartanProfiles
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact profile family for every nonnegative real scale -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology NNReal

variable {EG G I W A : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1000000 in
include T in
/-- All nonnegative scales share one modulus of continuity. -/
theorem equicontinuous_all_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (scale : A → ℝ) (hs0 : ∀ u, 0 ≤ scale u)
    {K : ℝ≥0} (J : A → G → W) (hJ : ∀ u, LipschitzWith K (J u))
    (x suffix : A → G) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    Equicontinuous (fun u => rescaledMapProfile (J u) (x u) (suffix u) (scale u)
      (fun z => F.inclusionD (F.ExpD (F.D.equiv
        ((exponentialRescaleBasis b cost (scale u)).equivFun.symm z))))) := by
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords k) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let E : H → G := fun v => F.inclusionD (F.ExpD (F.D.equiv v))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbij : Function.Bijective (F.ExpD ∘ F.D.equiv) :=
    (funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD
    F.isExpD hk 2
  have hm (v w : H) : E (finiteDynkinPolynomial coeff ![v, w]) = E v * E w := by
    simpa [E, List.ofFn_succ] using congrArg F.inclusionD (hprod ![v, w]).symm
  obtain ⟨C, hC, hmetric⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD
    dynkinD X hk hletters b₀ 1
  have hchart : Continuous (fun p : ℝ × (Fin (finrank ℝ H) → ℝ) =>
      E ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)) := by
    exact F.closedD.continuous.comp ((funext hchartD ▸ chartD.continuous).comp
      (continuous_mapped_scaled_basis_coordinates F.D.equiv.toLinearMap b cost))
  exact equicontinuous_all_scale_profiles b cost
    (maximizing_word_basis_bracket_weight X hk b₀ (fun _ => 1) β hβ) E
    (F.closedD.injective.comp hbij.injective)
    (by simp [E, F.isExpD.map_zero]) (fun v => by simp [E, F.isExpD.map_neg])
    (fun v s t => by simp only [E, map_smul, F.isExpD.map_add_smul, map_mul])
    coeff hm hC (hmetric β hβ) hchart scale hs0 J hJ x suffix

variable [ProperSpace W]

set_option maxHeartbeats 1000000 in
include T in
/-- The compact family is chosen before the real scale, the map, the
center, and the suffix. This makes subsequent enlargement thresholds
independent of any selected sequence. -/
theorem exists_universal_compact_cartan_profiles_all_scales
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (K : ℝ≥0) (B : ℝ) :
    ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∀ r : ℝ, 0 ≤ r → ∀ J : G → W, LipschitzWith K J → ∀ x a : G,
      dist 1 a / Real.exp r ≤ B → ∃ f ∈ S, ∀ z,
        f z = rescaledMapProfile J x a r
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
              (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) r).equivFun.symm z)))) z := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let P := AllScaleProfileData G W K B
  let b := WordBasisSelections.basis X (boundedBracketWords k) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let φ := fun r z => F.inclusionD (F.ExpD (F.D.equiv
    ((exponentialRescaleBasis b cost r).equivFun.symm z)))
  have hφ (r : ℝ) : Continuous (φ r) :=
    F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
      F.D.equiv (F.D.tangent_nilpotent inferInstance) (exponentialRescaleBasis b cost r))
  have hz (r : ℝ) : φ r 0 = 1 := by simp [φ, F.isExpD.map_zero]
  let raw : P → C((Fin (finrank ℝ H) → ℝ), W) := fun p =>
    ⟨rescaledMapProfile p.map p.center p.suffix p.scale (φ p.scale),
      continuous_rescaledMapProfile p.lipschitz.continuous _ _ _ (hφ p.scale)⟩
  have hequi : Equicontinuous (fun p z => raw p z) :=
    equicontinuous_all_cartan_profiles T F hExpG realize haarD dynkinD X hk hletters b₀ β hβ
      (fun p : P => p.scale) (fun p => p.nonneg) (fun p => p.map) (fun p => p.lipschitz)
      (fun p => p.center) (fun p => p.suffix)
  obtain ⟨S, hS, hmem⟩ := exists_compact_containing_profiles raw hequi (0 : W) (by
    intro z
    obtain ⟨D, _, hD⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD dynkinD
      X hk hletters b₀ ‖z‖
    refine ⟨(K : ℝ) * D + (K : ℝ) * B, ?_⟩
    intro p
    rw [dist_zero_right]
    have hchart : dist 1 (φ p.scale z) / Real.exp p.scale ≤ D := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      apply hD β hβ p.scale p.nonneg
      rw [LinearEquiv.apply_symm_apply]
    have hanchor := (rescaledMapProfile_zero_norm_le p.lipschitz p.center p.suffix
      p.scale (φ p.scale) (hz p.scale)).trans
      (mul_le_mul_of_nonneg_left p.suffix_bound K.coe_nonneg)
    exact (rescaledMapProfile_norm_le p.lipschitz p.center p.suffix p.scale
      (φ p.scale) (hz p.scale) z).trans
      (add_le_add (mul_le_mul_of_nonneg_left hchart K.coe_nonneg) hanchor))
  refine ⟨S, hS, ?_⟩
  intro r hr J hJ x a ha
  let p : P := ⟨r, hr, J, hJ, x, a, ha⟩
  exact ⟨raw p, hmem p, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPublishedRawChain
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-chain concentration from the precisely published inputs -/

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
/-- The compact profile family is constructed before the enlargement threshold,
uniformly in all maps and centers. The conclusion concerns the original raw
profiles and assumes no compactness or convergence for their laws. -/
theorem exists_uniform_published_raw_chain_concentration_oai
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
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n),
      ∀ Z : Set (Fin (finrank ℝ H) → ℝ), ∀ _ : CompactSpace Z,
      (∀ z ∈ Z, eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (radius : ℕ → ℝ) (_hr0 : ∀ n, 0 ≤ radius n)
    (_hr : HasSubexponentialUpperBoundSeq scale radius)
    {N : ℕ} (base : ℕ → Fin (N + 1) → F.N.carrier)
    (step : ℕ → Fin N → F.N.carrier)
    (_hbase : ∀ n j, base n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hstep : ∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hnext : ∀ n j, base n j.succ = base n j.castSucc * step n j)
    (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ)
    (_htime : ∀ n j, |time n j| ≤ radius n * Real.exp
      ((M.weight (mode n j) (pivot (mode n j)) + δ * B) * scale n))
    (_hroot : ∀ n j, F.inclusionN (step n j) =
      Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (raw : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (_hraw : ∀ n q z, raw n q z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z)
    (_hmetric : ∀ᶠ n in atTop, ∀ j q, q ∈ (fun v => v * base n j) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 →
      dist 1 (F.inclusionN q) / scale n ≤ C)
    (j : Fin (N + 1)) {η : ℝ} (_hη : 0 < η),
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (scale n) 1 : Measure F.N.carrier)
      {q | η ≤ dist ((raw n (q * base n j)).restrict Z)
        ((raw n (q * base n 0)).restrict Z)}) atTop (𝓝 0) := by
  obtain ⟨S, hS, hmem⟩ := exists_universal_compact_cartan_profiles_all_scales (W := W) T F
    hExp realize haarD dynkinD X hDnil hDletters bD₀ βD hβD (Kπ * Λ) C
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨δ₀, hδ₀, hconc⟩ := M.exists_uniform_published_chain_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber S hS hnz
    sourceInputs sourceDynkin targetInputs
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 Z hZ hZheight pair center radius hr0 hradius N base step
    hbase hstep hnext mode time htime hroot raw hraw hmetric j η hη
  let r := fun n => max (Real.log (scale n)) 0
  have hr n : r n = Real.log (scale n) := max_eq_left (Real.log_nonneg (hs1 n))
  have hexp n : Real.exp (r n) = scale n := by
    rw [hr, Real.exp_log (zero_lt_one.trans_le (hs1 n))]
  let := hZ
  let J := fun n g => (π ((pair n).val.1 g)).toAdd
  have hJ n : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (pair n).property.1.1
  let φ := fun n => F.profileChart (exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n))
  have hφ n : Continuous (φ n) :=
    F.continuous_profileChart (funext hchartD ▸ chartD.continuous) _
  let cells := fun n => {q : F.N.carrier | dist 1 (F.inclusionN q) / scale n ≤ C}
  have hcells n : MeasurableSet (cells n) :=
    (isClosed_le ((continuous_const.dist F.closedN.continuous).div_const _) continuous_const).measurableSet
  have hcellne n : (cells n).Nonempty := ⟨1, by
    change dist 1 (F.inclusionN 1) / scale n ≤ C
    simpa only [map_one, dist_self, zero_div] using hC⟩
  have hm n q (hq : q ∈ cells n) :
      rescaledContinuousProfile (J n) (hJ n).continuous (center n) (F.inclusionN q)
        (r n) (φ n) (hφ n) ∈ S := by
    obtain ⟨f, hf, he⟩ := hmem (r n) (le_max_right _ _) (J n) (hJ n) (center n) (F.inclusionN q)
      (by simpa only [hexp] using (show dist 1 (F.inclusionN q) / scale n ≤ C from hq))
    have heq : rescaledContinuousProfile (J n) (hJ n).continuous (center n)
        (F.inclusionN q) (r n) (φ n) (hφ n) = f := by
      ext z
      exact (he z).symm
    exact heq ▸ hf
  have hprofiles n := exists_measurable_borel_sampled_profile (J n) (hJ n).continuous
    (center n) (r n) (φ n) (hφ n) F.inclusionN F.closedN.continuous.measurable
    (cells n) (hcells n) (hcellne n) S (hm n)
  choose profile hp ha using hprofiles
  have heq n q (hq : q ∈ cells n) : (profile n q).val = raw n q := by
    ext z
    exact (ha n q hq z).trans (hraw n q z).symm
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hmetric
  have hm' n := hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  have hc' := hconc δ hδ hd Z hZ hZheight
    (fun n => scale (n + n₀)) (hgrows.comp (tendsto_add_atTop_nat n₀))
    (hmono.comp (strictMono_id.add_const n₀)) (fun n => hs1 (n + n₀))
    (fun n => pair (n + n₀)) (fun n => center (n + n₀))
    (fun n => radius (n + n₀)) (fun n => hr0 (n + n₀))
    (fun ε hε => (tendsto_add_atTop_nat n₀).eventually (hradius ε hε))
    (fun n => base (n + n₀)) (fun n => step (n + n₀))
    (fun n => hbase (n + n₀)) (fun n => hstep (n + n₀)) (fun n => hnext (n + n₀))
    (fun n => mode (n + n₀)) (fun n => time (n + n₀))
    (fun n => htime (n + n₀)) (fun n => hroot (n + n₀))
    (fun n => profile (n + n₀)) (fun n => hp (n + n₀))
    (fun n k q hq z => ha (n + n₀) q (hm' n k q hq) z) j hη
  apply (tendsto_add_atTop_iff_nat n₀).mp
  apply hc'.congr'
  filter_upwards [] with n
  apply measure_congr
  have hprops := M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN bN Eall γ (scale (n + n₀)) 1
  filter_upwards [ae_mem_cellProbabilityMeasure _ _ hprops.1 hprops.2.1 hprops.2.2] with q hq
  have hq' : q ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale (n + n₀)) 1 := by
    simpa only [mul_one, image_id'] using hq
  have hj := heq (n + n₀) (q * base (n + n₀) j) (hm' n j _ ⟨q, hq', rfl⟩)
  have hz := heq (n + n₀) (q * base (n + n₀) 0) (hm' n 0 _ ⟨q, hq', rfl⟩)
  -- after `filter_upwards` on `=ᵐ` of sets our goal is the applied sets
  change (η ≤ dist ((profile (n + n₀) (q * base (n + n₀) j)).val.restrict Z)
      ((profile (n + n₀) (q * base (n + n₀) 0)).val.restrict Z)) =
    (η ≤ dist ((raw (n + n₀) (q * base (n + n₀) j)).restrict Z)
      ((raw (n + n₀) (q * base (n + n₀) 0)).restrict Z))
  rw [hj, hz]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_raw_chain_concentration_oai
