-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:57:22.562875+00:00
-- url     : https://prove2.me/submissions/6fa7a5e0-4b88-4934-a1b9-7dfad040d9af

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

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

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bound on bilinear evaluations bounds the iterated operator norm. -/
theorem norm_bilinear_le_of_bound (B : V →L[ℝ] V →L[ℝ] V) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound B hC
  intro x
  apply ContinuousLinearMap.opNorm_le_bound (B x) (mul_nonneg hC (norm_nonneg x))
  exact h x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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
theorem isClosed_wordNormalizations [Fintype I] {J : Type*}
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

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
theorem bilinearOrbitSpan_eq_top {J : Type*}
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
theorem exists_bilinearOrbit_basis {J : Type*}
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

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
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

theorem bracketWordLength_eq_nodes_add_one {I : Type*} (w : FreeMagma I) :
    bracketWordLength w = bracketWordNodes w + 1 := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv => simp only [bracketWordLength, bracketWordNodes, hu, hv]; omega

/-- Evaluation of each Lie word is bounded by the number of its brackets and
letters. This is uniform over a family with bounded structure constants. -/
theorem norm_basis_evalBracketWord_le {I : Type*} (X : I → L)
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

@[simp] theorem rightNestedWord_length {I : Type*} (d : ℕ) (f : Fin (d + 1) → I) :
    bracketWordLength (rightNestedWord d f) = d + 1 := by
  rw [bracketWordLength_eq_nodes_add_one, rightNestedWord_nodes]

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
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
theorem repr_exponentialRescaleBasis_bracket {J : Type*}
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The polynomial product estimate in any basis with bounded brackets. -/
theorem product_mem_exponentialCoordinateBox
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ L)
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

variable {I : Type*} [Fintype I] [DecidableEq I]

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

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

variable {I : Type*}

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

variable {I Y : Type*} {k : ℕ}

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedInverseCoding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous generator coding on a whole bounded logarithmic box

A continuous local inverse suffices: divide the logarithm by a fixed
integer, use the local inverse, and repeat its word. This keeps the
combinatorial pattern fixed and makes every amplitude continuous on the
entire prescribed box. In particular, these selectors can be sampled
independently of the starting sheet.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {V L I G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup L] [Module ℝ L] [Group G]

/-- Upgrade a continuous small-logarithm scheme to any fixed bounded box,
without a measurable-selection theorem or a parameter-dependent word length. -/
theorem bounded_continuous_generator_coding
    (X : I → L) (Exp : L → G) (q : V →ₗ[ℝ] L)
    (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    {ε : ℝ} {N : ℕ} {C : ℝ}
    {d : ℕ} (w : Fin d → List (I × ℝ)) (i : Fin d → I)
    (σ : V → Fin d → ℝ) (hσ : ContinuousOn σ (ball 0 ε))
    (hlocal : ∀ y ∈ ball (0 : V) ε,
      (generatorSchemeWord w i (σ y)).length ≤ N ∧
      (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
      generatorGroupWord X Exp (generatorSchemeWord w i (σ y)) = Exp (q y))
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk0 : (0 : ℝ) < k)
    (hkR : R < (k : ℝ) * ε) :
    ∃ word : List (I × (closedBall (0 : V) R → ℝ)),
      word.length ≤ k * N ∧ (∀ z ∈ word, Continuous z.2) ∧
      (∀ y, ∀ z ∈ word, |z.2 y| ≤ C) ∧
      ∀ y, generatorGroupWord X Exp (word.map (fun z => (z.1, z.2 y))) = Exp (q y.val) := by
  let Y := closedBall (0 : V) R
  let small : Y → V := fun y => (k : ℝ)⁻¹ • y.val
  have hsmall (y : Y) : small y ∈ ball (0 : V) ε := by
    rw [mem_ball, dist_zero_right]
    dsimp only [small]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), ← div_eq_inv_mul]
    apply (div_lt_iff₀ hk0).mpr
    have hy : ‖y.val‖ ≤ R := by
      have hy : y.val ∈ closedBall (0 : V) R := y.property
      simpa only [mem_closedBall, dist_zero_right] using hy
    exact hy.trans_lt (by simpa only [mul_comm] using hkR)
  have hsmallcont : Continuous small := continuous_const.smul continuous_subtype_val
  let τ : Y → Fin d → ℝ := σ ∘ small
  have hτ : Continuous τ := hσ.comp_continuous hsmallcont hsmall
  let u := parameterGeneratorSchemeWord w i τ
  let word := (List.replicate k u).flatten
  have heval (y : Y) : word.map (fun z => (z.1, z.2 y)) =
      (List.replicate k (generatorSchemeWord w i (τ y))).flatten := by
    simp only [word, List.map_flatten, List.map_replicate, u,
      parameterGeneratorSchemeWord_eval]
  have hlen : u.length ≤ N := by
    let y : Y := ⟨0, by
      change (0 : V) ∈ closedBall (0 : V) R
      simpa only [mem_closedBall, dist_self] using hR⟩
    have hh := (hlocal _ (hsmall y)).1
    change (generatorSchemeWord w i (τ y)).length ≤ N at hh
    rw [← parameterGeneratorSchemeWord_eval w i τ y, List.length_map] at hh
    exact hh
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · simpa only [word, List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul] using Nat.mul_le_mul_left k hlen
  · intro z hz
    obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hv
    exact parameterGeneratorSchemeWord_continuous w i τ hτ z hz
  · intro y z hz
    obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hv
    have hz' : (z.1, z.2 y) ∈ generatorSchemeWord w i (τ y) := by
      rw [← parameterGeneratorSchemeWord_eval w i τ y]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    exact (hlocal _ (hsmall y)).2.1 _ hz'
  · intro y
    rw [heval]
    have hpow : ∀ v : L, ∀ n : ℕ, Exp ((n : ℝ) • v) = (Exp v) ^ n := by
      intro v n
      induction n with
      | zero => simp [hzero]
      | succ n ih => rw [Nat.cast_add, Nat.cast_one, hadd, ih, one_smul, pow_succ]
    calc
      generatorGroupWord X Exp ((List.replicate k (generatorSchemeWord w i (τ y))).flatten) =
          (generatorGroupWord X Exp (generatorSchemeWord w i (τ y))) ^ k := by
        simp only [generatorGroupWord, List.map_flatten, List.map_replicate,
          List.prod_flatten, List.prod_replicate]
      _ = (Exp (q (small y))) ^ k := congrArg (fun g : G => g ^ k) (hlocal _ (hsmall y)).2.2
      _ = Exp ((k : ℝ) • q (small y)) := (hpow _ _).symm
      _ = Exp (q y.val) := by
        simp only [small, map_smul, smul_smul, mul_inv_cancel₀ hk0.ne', one_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConePolarTemplate
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar templates and their exact vanishing directions

The compact unit slice of the negative polar has support zero on the cone
and strictly positive support at every functional outside the cone. These
are the widths used in the cone-ideal covering argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem zero_mem_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    (0 : W) ∈ conePolarTemplate C := by
  simp [conePolarTemplate]

theorem isCompact_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    IsCompact (conePolarTemplate C) := by
  have hc : IsClosed {x : W | ∀ β ∈ C, β x ≤ 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun β => isClosed_iInter fun _ =>
      isClosed_le β.continuous continuous_const
  exact (isCompact_closedBall (0 : W) 1).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter hc) (fun x hx => by
      simpa only [mem_closedBall, dist_zero_right] using hx.1)

omit [FiniteDimensional ℝ W] in
theorem convex_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    Convex ℝ (conePolarTemplate C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
        (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = 1 := by linarith
  · intro β hβ
    simpa only [map_add, map_smul, smul_eq_mul, add_zero] using
      add_le_add (mul_nonpos_of_nonneg_of_nonpos ha (hx.2 β hβ))
        (mul_nonpos_of_nonneg_of_nonpos hb (hy.2 β hβ))

theorem conePolarWidth_nonneg (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) : 0 ≤ conePolarWidth C β := by
  apply le_csSup ((isCompact_conePolarTemplate C).image β.continuous).bddAbove
  exact ⟨0, zero_mem_conePolarTemplate C, β.map_zero⟩

theorem conePolarWidth_eq_zero (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∈ C) : conePolarWidth C β = 0 := by
  apply le_antisymm _ (conePolarWidth_nonneg C β)
  change sSup (β '' conePolarTemplate C) ≤ 0
  have hne : (β '' conePolarTemplate C).Nonempty :=
    ⟨β 0, 0, zero_mem_conePolarTemplate C, rfl⟩
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2 β hβ

/-- Dilating the polar template multiplies every supporting width by the
same scalar, so a maximizing word basis works for every positive radius. -/
theorem conePolarWidth_smul (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) {a : ℝ} (ha : 0 ≤ a) :
    sSup (β '' ((fun x : W => a • x) '' conePolarTemplate C)) =
      a * conePolarWidth C β := by
  have hcompact := isCompact_conePolarTemplate C
  have hne : (conePolarTemplate C).Nonempty := ⟨0, zero_mem_conePolarTemplate C⟩
  obtain ⟨x, hx, heq⟩ := hcompact.exists_sSup_image_eq hne β.continuous.continuousOn
  have him := hcompact.image (show Continuous (fun x : W => a • x) from continuous_const.smul continuous_id)
  apply le_antisymm
  · apply csSup_le ((hne.image _).image β)
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (hcompact.image β.continuous).bddAbove ⟨y, hy, rfl⟩) ha
  · change a * sSup (β '' conePolarTemplate C) ≤ _
    rw [heq]
    exact le_csSup (him.image β.continuous).bddAbove
      ⟨a • x, ⟨x, hx, rfl⟩, by simp⟩

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
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

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Exponential coordinates transfer the genuine group axioms, rather than
postulating them for a limiting polynomial. -/
theorem polynomialGroupLaws_of_exp {G : Type*} [Group G]
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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

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

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
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

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

/-- The actual polynomial group laws define a closed part of the compact
normalized Lie parameter space. -/
theorem isCompact_normalizedGroupParameters {c : ℕ} (a : DynkinCoefficients c 2)
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedGroupParameters a w b C) :=
  (isCompact_normalizedLieParameters w b C).inter_right
    ((isClosed_dynkinGroupLaws a).preimage continuous_fst)

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  {G : Type*} [Group G]

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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

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

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

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

variable {G A : Type*} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

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

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

variable {V P I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
theorem exists_coordinate_basis_scheme {J : Type*} {c : ℕ}
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

variable {P E F : Type*}
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

theorem finite_positive_lower_bound {I : Type*} (s : Finset I)
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

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

theorem isCompact_normalizedExponentialParameters {c : ℕ}
    (a : DynkinCoefficients c 2) (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedExponentialParameters a w b C) :=
  (isCompact_normalizedGroupParameters a w b C).inter_right
    ((isClosed_exponentialConjugationLaw a).preimage continuous_fst)

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [DecidableEq I] {G A : Type*} [Group G]
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

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

variable {I : Type*} [Fintype I] [FiniteDimensional ℝ V]

/-- Every limiting normalized law admits a polynomial generator scheme with
surjective amplitude differential at the identity. -/
theorem exists_coordinate_submersive_scheme {J : Type*} {c : ℕ}
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

variable {P E F : Type*}
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

variable {P E F J : Type*}
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

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Measurable endpoint coding for every actual normalized law: the inverse
is continuous on the common ball, and all its amplitudes are bounded by one. -/
theorem exists_uniform_coordinate_inverse_sections {J : Type*} {c : ℕ}
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

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
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
theorem exists_uniform_bounded_coordinate_inverse {J : Type*} {c : ℕ}
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledWordPrefixes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coordinate bounds for every prefix of a bounded generator word

This is the prefix control needed to apply the neighboring-sheet argument
to words supplied by uniform generation. Both the word length and the
normalized amplitudes are bounded; the box shape and scale may vary.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [FiniteDimensional ℝ L] in
/-- Every prefix of every bounded normalized generator word remains in a
single uniformly enlarged rescaled box. -/
theorem exists_uniform_rescaled_word_prefix_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords c)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords c)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ u : List (I × ℝ), u.length ≤ N →
      (∀ z ∈ u, |z.2| ≤ A) → ∀ j : ℕ,
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) ∈
        exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
            (fun k => bracketWordExponent s (β.val k)) r) D := by
  obtain ⟨R, hR, hgen⟩ := exists_uniform_rescaled_generator_bound
    X (boundedBracketWords c) hletters b₀
  obtain ⟨K, hK, hprod⟩ := exists_uniform_word_box_product_bound dynkin e Exp hExp X hc b₀
  let D := K * (1 + (N : ℝ)) ^ c * (1 + A * R) ^ c
  refine ⟨D, by dsimp [D] <;> positivity, ?_⟩
  intro s β hβ r hr u hu hamp j
  let v := u.take j
  let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
    (fun k => bracketWordExponent s (β.val k)) r
  let g := fun k : Fin v.length => Exp (e ((v.get k).2 • (Real.exp (r * s (v.get k).1) • X (v.get k).1)))
  have hg (k : Fin v.length) : g k ∈ exponentialCoordinateBox (Exp ∘ e) b (A * R) := by
    refine ⟨(v.get k).2 • (Real.exp (r * s (v.get k).1) • X (v.get k).1), rfl, ?_⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hamp _ (List.mem_of_mem_take (List.get_mem v k)))
      (hgen s β hβ r hr _) (norm_nonneg _) hA
  have hp := hprod s β hβ r hr v.length (A * R) (mul_nonneg hA hR) g hg
  have hlist : List.ofFn g = v.map (fun z : I × ℝ =>
      Exp (e (z.2 • (Real.exp (r * s z.1) • X z.1)))) := by
    dsimp only [g]
    rw [List.ofFn_comp' v.get (fun z : I × ℝ =>
      Exp (e (z.2 • (Real.exp (r * s z.1) • X z.1)))), List.ofFn_get]
  rw [hlist] at hp
  change generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) v ∈
    exponentialCoordinateBox (Exp ∘ e) b
      (K * (1 + (v.length : ℝ)) ^ c * (1 + A * R) ^ c) at hp
  obtain ⟨x, hx, hbound⟩ := hp
  refine ⟨x, hx, hbound.trans ?_⟩
  have hlen : v.length ≤ N := by
    simpa only [v, List.length_take] using (Nat.min_le_right j u.length).trans hu
  have hlen' : (v.length : ℝ) ≤ N := by exact_mod_cast hlen
  dsimp only [D]
  gcongr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DominatedWordPrefixes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded prefixes when a smaller template is used for generation -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Uniform generation in a smaller template does not force a change of the
ambient maximizing basis. Shrinking each normalized letter amplitude
places every prefix in a fixed-radius box for the larger template. -/
theorem exists_uniform_dominated_word_prefix_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords c)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s t : I → ℝ), (∀ i, s i ≤ t i) →
      ∀ β : WordBasisSelections X (boundedBracketWords c),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent t w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ u : List (I × ℝ), u.length ≤ N →
      (∀ z ∈ u, |z.2| ≤ A) → ∀ j : ℕ,
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) ∈
        exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
            (fun k => bracketWordExponent t (β.val k)) r) D := by
  obtain ⟨D, hD, hprefix⟩ := exists_uniform_rescaled_word_prefix_bound
    dynkin e Exp hExp X hc hletters b₀ N hA
  refine ⟨D, hD, ?_⟩
  intro s t hst β hβ r hr u hu hamp j
  let renorm := fun z : I × ℝ => (z.1, z.2 * Real.exp (r * (s z.1 - t z.1)))
  have hrenorm (z : I × ℝ) : |(renorm z).2| ≤ |z.2| := by
    change |z.2 * Real.exp (r * (s z.1 - t z.1))| ≤ |z.2|
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ |z.2| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hst z.1))))
        (abs_nonneg _)
      _ = _ := mul_one _
  have hh := hprefix t β hβ r hr (u.map renorm)
    (by simpa only [List.length_map] using hu)
    (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact (hrenorm y).trans (hamp y hy)) j
  have hword : generatorGroupWord (fun i => Real.exp (r * t i) • X i)
      (Exp ∘ e) ((u.map renorm).take j) =
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) := by
    simp only [generatorGroupWord, ← List.map_take, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    apply congrArg (Exp ∘ e)
    change (z.2 * Real.exp (r * (s z.1 - t z.1))) •
      (Real.exp (r * t z.1) • X z.1) = z.2 • (Real.exp (r * s z.1) • X z.1)
    rw [smul_smul, smul_smul, mul_assoc, ← Real.exp_add]
    rw [show r * (s z.1 - t z.1) + r * t z.1 = r * s z.1 by ring]
  rwa [hword] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorWordPadding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-length generator words and their consecutive prefixes -/

noncomputable section
namespace PolycyclicRecognition

variable {I L G : Type*} [AddCommMonoid L] [Module ℝ L] [Group G]
  (X : I → L) (Exp : L → G)

/-- Appending zero-amplitude letters changes no prefix product. -/
theorem generatorGroupWord_zero_padding
    (hzero : Exp 0 = 1)
    (i₀ : I) (u : List (I × ℝ)) (n j : ℕ) :
    generatorGroupWord X Exp ((u ++ List.replicate n (i₀, 0)).take j) =
      generatorGroupWord X Exp (u.take j) := by
  simp only [List.take_append, List.take_replicate]
  simp [generatorGroupWord, hzero]

/-- Consecutive prefix products differ by precisely the next generator. -/
theorem generatorGroupWord_take_succ
    (u : List (I × ℝ)) (j : ℕ) (hj : j < u.length) :
    generatorGroupWord X Exp (u.take (j + 1)) =
      generatorGroupWord X Exp (u.take j) * Exp (u[j].2 • X u[j].1) := by
  rw [← List.take_concat_get' u j hj]
  simp only [generatorGroupWord, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MeasurableGeneratorPrefixes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable prefixes of the fixed generator schemes

The bounded local inverse construction fixes the letter pattern. Only its
real parameters vary; hence all actual prefixes and their global logarithms
are measurable, including after an independently sampled initial suffix.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

/-- A fixed finite word with measurable real parameters has a measurable
endpoint. This includes every prefix of a bounded generator scheme. -/
theorem measurable_fixed_generator_word
    {A I G : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [Group G] [MeasurableMul₂ G]
    (f : I → ℝ → G) (hf : ∀ i, Measurable (f i))
    (word : List (I × (A → ℝ))) (hw : ∀ z ∈ word, Measurable z.2) :
    Measurable (fun a => (word.map (fun z => f z.1 (z.2 a))).prod) := by
  induction word with
  | nil => simpa only [List.map_nil, List.prod_nil] using measurable_const
  | cons z word ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ((hf z.1).comp (hw z (List.mem_cons_self))).mul
        (ih (fun w hw' => hw w (List.mem_cons_of_mem _ hw')))

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

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]

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

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [Fintype I] [DecidableEq I]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasurableGeneratorChain
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-length measurable chains from the bounded template selectors -/

noncomputable section
namespace PolycyclicRecognition

/-- Padding uses a fixed zero letter. The selected letter pattern is
independent of the sampled endpoint, and every prefix is measurable. -/
theorem exists_measurable_generator_chain
    {A I L G : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [AddCommMonoid L] [Module ℝ L] [Group G] [MeasurableMul₂ G]
    (X : I → L) (Exp : L → G) (hzero : Exp 0 = 1)
    (hf : ∀ i, Measurable (fun t : ℝ => Exp (t • X i)))
    (i₀ : I) (word : List (I × (A → ℝ)))
    (hw : ∀ z ∈ word, Measurable z.2)
    {N : ℕ} (hlen : word.length ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hamp : ∀ a, ∀ z ∈ word, |z.2 a| ≤ C)
    (base : A → G) (hbase : Measurable base) :
    ∃ (mode : Fin N → I) (coeff : A → Fin N → ℝ)
      (vertex : A → Fin (N + 1) → G),
      (∀ j, Measurable (fun a => coeff a j)) ∧
      (∀ j, Measurable (fun a => vertex a j)) ∧
      (∀ a j, |coeff a j| ≤ C) ∧
      (∀ a, vertex a 0 = base a) ∧
      (∀ a, vertex a (Fin.last N) = base a *
        generatorGroupWord X Exp (word.map (fun z => (z.1, z.2 a)))) ∧
      (∀ a j, vertex a j.succ = vertex a j.castSucc * Exp (coeff a j • X (mode j))) ∧
      (∀ a j, vertex a j = base a *
        generatorGroupWord X Exp ((word.map (fun z => (z.1, z.2 a))).take j.val)) := by
  classical
  let padded := word ++ List.replicate (N - word.length) (i₀, fun _ : A => (0 : ℝ))
  have hp : padded.length = N := by
    simp only [padded, List.length_append, List.length_replicate]
    omega
  have hpmeas : ∀ z ∈ padded, Measurable z.2 := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw z hz
    · obtain rfl := List.eq_of_mem_replicate hz
      exact measurable_const
  have hpa : ∀ a, ∀ z ∈ padded, |z.2 a| ≤ C := by
    intro a z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hamp a z hz
    · obtain rfl := List.eq_of_mem_replicate hz
      simpa only [abs_zero] using hC
  let step (j : Fin N) := padded[j.val]'(by rw [hp]; exact j.isLt)
  let coeff (a : A) (j : Fin N) := (step j).2 a
  let vertex (a : A) (j : Fin (N + 1)) := base a *
    generatorGroupWord X Exp ((padded.map (fun z => (z.1, z.2 a))).take j.val)
  have hprefix (a : A) (j : ℕ) :
      generatorGroupWord X Exp ((padded.map (fun z => (z.1, z.2 a))).take j) =
        generatorGroupWord X Exp ((word.map (fun z => (z.1, z.2 a))).take j) := by
    simpa only [padded, List.map_append, List.map_replicate] using
      generatorGroupWord_zero_padding X Exp hzero i₀
        (word.map (fun z => (z.1, z.2 a))) (N - word.length) j
  refine ⟨fun j => (step j).1, coeff, vertex, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hpmeas _ (List.getElem_mem _)
  · intro j
    apply hbase.mul
    have he (a : A) : generatorGroupWord X Exp
        ((padded.map (fun z => (z.1, z.2 a))).take j.val) =
        ((padded.take j.val).map (fun z => Exp (z.2 a • X z.1))).prod := by
      simp only [← List.map_take, generatorGroupWord, List.map_map, Function.comp_def]
    simp_rw [he]
    exact measurable_fixed_generator_word (fun i t => Exp (t • X i)) hf
      (padded.take j.val) (fun z hz => hpmeas z (List.mem_of_mem_take hz))
  · intro a j
    exact hpa a _ (List.getElem_mem _)
  · intro a
    simp only [vertex, Fin.val_zero, List.take_zero, generatorGroupWord_nil, mul_one]
  · intro a
    change base a * generatorGroupWord X Exp
      ((padded.map (fun z => (z.1, z.2 a))).take N) = _
    rw [hprefix]
    rw [List.take_of_length_le (by simpa only [List.length_map] using hlen)]
  · intro a j
    change base a * generatorGroupWord X Exp
      ((padded.map (fun z => (z.1, z.2 a))).take (j.val + 1)) =
      (base a * generatorGroupWord X Exp
        ((padded.map (fun z => (z.1, z.2 a))).take j.val)) * _
    have hs := generatorGroupWord_take_succ X Exp
      (padded.map (fun z => (z.1, z.2 a))) j.val (by
        simpa only [List.length_map, hp] using j.isLt)
    rw [hs, mul_assoc]
    simp only [List.getElem_map, coeff, step]
  · intro a j
    exact congrArg (base a * ·) (hprefix a j.val)

end PolycyclicRecognition

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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateSections
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
/-- Common continuous endpoint coding for all actual Cartan rescalings. -/
theorem exists_uniform_template_inverse_sections
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (β : M.Bases),
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
          (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
        ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
          (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
          (σ : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
            Fin (finrank ℝ (cartanRootIdeal H)) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
              (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i (σ y)) =
                F.ExpN (F.N.equiv (b.equivFun.symm y)) := by
  obtain ⟨ε, N, C, hε, hC, hcode⟩ := M.exists_uniform_cartan_inverse_sections T F
    hExpG realize haarN dynkinN b₀
  exact ⟨ε, N, C, hε, hC, fun β hβ r hr =>
    hcode (M.templateSupportExponent v) β hβ r hr⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoundedTemplatePaths
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous probe paths on an entire bounded Cartan box

The local inverse scheme is repeated after dividing logarithms by one
fixed integer. Both the number of switches and their amplitudes are
uniform over the scale and maximizing basis. Every path sample remains
continuous in the original box coordinate, which supplies the measurable
choices required in the independent-probe argument.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
omit [IsIsometricSMul G G] in
theorem exists_continuous_bounded_template_coding
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∃ word : List (Fin M.letterCount ×
          (closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R → ℝ)),
        word.length ≤ N ∧ (∀ z ∈ word, Continuous z.2) ∧
        (∀ y, ∀ z ∈ word, |z.2 y| ≤ C) ∧
        ∀ y, generatorGroupWord
          (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) (word.map (fun z => (z.1, z.2 y))) =
            F.ExpN (F.N.equiv (b.equivFun.symm y.val)) := by
  obtain ⟨ε, N, C, hε, hC, hcode⟩ :=
    M.exists_uniform_template_inverse_sections T F hExp realize haarN dynkinN b₀ v
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / ε) 0)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : R < (k : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hk)
  refine ⟨k * N, C, hC, ?_⟩
  intro r hr β hβ b
  obtain ⟨w, i, σ, hσ, hs⟩ := hcode β hβ r hr
  apply bounded_continuous_generator_coding
    (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
    (F.ExpN ∘ F.N.equiv) b.equivFun.symm.toLinearMap
    (by simp [F.isExpN.map_zero])
    (fun x s t => by
      simpa only [Function.comp_apply, map_smul] using
        F.isExpN.map_add_smul (F.N.equiv x) s t)
    w i σ hσ (fun y hy => ⟨(hs y hy).2.1, (hs y hy).2.2⟩) R hR k hk0 hkR

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasurableTemplateCoding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable template words for independently sampled probe endpoints -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Metric
open scoped Manifold

variable {EG G A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [MeasurableSpace A]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
/-- A Borel endpoint sampler in a bounded box admits a fixed letter pattern
with Borel bounded parameters. The length and amplitude constants work at
every scale and for every maximizing basis. -/
theorem exists_measurable_bounded_template_coding
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ word : List (Fin M.letterCount × (A → ℝ)),
        word.length ≤ N ∧ (∀ z ∈ word, Measurable z.2) ∧
        (∀ x, ∀ z ∈ word, |z.2 x| ≤ C) ∧
        ∀ x, generatorGroupWord
          (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) (word.map (fun z => (z.1, z.2 x))) =
            F.ExpN (F.N.equiv (b.equivFun.symm (y x).val)) := by
  obtain ⟨N, C, hC, hcode⟩ := M.exists_continuous_bounded_template_coding T F
    hExp realize haarN dynkinN b₀ v R hR
  refine ⟨N, C, hC, ?_⟩
  intro r hr β hβ b y hy
  obtain ⟨word, hlen, hw, hamp, hend⟩ := hcode r hr β hβ
  let word' := word.map (fun z => (z.1, z.2 ∘ y))
  refine ⟨word', ?_, ?_, ?_, ?_⟩
  · simpa only [word', List.length_map] using hlen
  · intro z hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact ((hw w hw').measurable).comp hy
  · intro x z hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact hamp (y x) w hw'
  · intro x
    simpa only [word', List.map_map, Function.comp_def] using hend (y x)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasurableGeneratorChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.exponentialRescaleBasis_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable actual Cartan chains with uniform prefix control -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Metric
open scoped Manifold

variable {EG G A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [MeasurableSpace A]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
include T in
/-- A sampled template endpoint admits a measurable chain of fixed length.
Every actual logarithmic prefix lies in a uniformly bounded larger box. -/
theorem exists_measurable_template_generator_chain
    [Nonempty (Fin M.letterCount)]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ r : ℝ, 0 ≤ r → ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      ∀ t : Fin M.letterCount → ℝ, (∀ i, M.templateSupportExponent v i ≤ t i) →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ (mode : Fin N → Fin M.letterCount) (coeff : A → Fin N → ℝ)
        (vertex : A → Fin (N + 1) → cartanRootIdeal H),
        (∀ j, Measurable (fun q => coeff q j)) ∧
        (∀ j, Measurable (fun q => b₀.equivFun (vertex q j))) ∧
        (∀ q j, |coeff q j| ≤ C * Real.exp (r * M.templateSupportExponent v (mode j))) ∧
        (∀ q, vertex q 0 = 0) ∧
        (∀ q, vertex q (Fin.last N) = b.equivFun.symm (y q).val) ∧
        (∀ q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) r).equivFun (vertex q j)‖ ≤ D) ∧
        ∀ q j, F.ExpN (F.N.equiv (vertex q j.succ)) =
          F.ExpN (F.N.equiv (vertex q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff q j • M.letter (mode j))) := by
  classical
  obtain ⟨N, C, hC, hcode⟩ := M.exists_measurable_bounded_template_coding (A := A) T F
    hExp realize haarN dynkinN b₀ v R hR
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨D, hD, hbound⟩ := exists_uniform_dominated_word_prefix_bound dynkinN
    F.N.equiv F.ExpN F.isExpN M.letter M.bound_zero M.letter_mem_wordList b₀ N hC0
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let e : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (b₀.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he (z) : e z = F.ExpN (F.N.equiv (b₀.equivFun.symm z)) := by
    change chart _ = _
    rw [hchart]
    rfl
  let : SecondCountableTopology F.N.carrier := e.symm.secondCountableTopology
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let E := F.ExpN ∘ F.N.equiv
  have hzero : E 0 = 1 := by simp [E, F.isExpN.map_zero]
  have hinj : Function.Injective E := (funext hchart ▸ chart.injective).comp F.N.equiv.injective
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro r hr β γ hβ t hst hγ b y hy
  obtain ⟨word, hlen, hmeas, hamp, hend⟩ := hcode r hr β hβ y hy
  let X := fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i
  have hflow (i) : Measurable (fun s : ℝ => E (s • X i)) := by
    have hc : Continuous (fun s : ℝ => e (s • b₀.equivFun (X i))) := e.continuous.comp
      (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => b₀.equivFun (X i))))
    have heq : (fun s : ℝ => e (s • b₀.equivFun (X i))) = (fun s => E (s • X i)) := by
      funext s
      rw [he, map_smul, LinearEquiv.symm_apply_apply]
      rfl
    rw [heq] at hc
    exact hc.measurable
  obtain ⟨mode, c, g, hc, hg, hampc, hg0, hgN, hstep, hprefix⟩ :=
    exists_measurable_generator_chain X E hzero hflow (Classical.choice inferInstance)
      word hmeas hlen hC0 hamp (fun _ => 1) measurable_const
  let vertex := fun q j => b₀.equivFun.symm (e.symm (g q j))
  have hEval (q j) : E (vertex q j) = g q j := by
    change F.ExpN (F.N.equiv (b₀.equivFun.symm (e.symm (g q j)))) = _
    rw [← he]
    exact e.apply_symm_apply _
  have hv0 (q) : vertex q 0 = 0 := by
    apply hinj
    rw [hEval, hg0, hzero]
  have hvN (q) : vertex q (Fin.last N) = b.equivFun.symm (y q).val := by
    apply hinj
    rw [hEval, hgN, one_mul]
    exact hend q
  refine ⟨mode, fun q j => c q j * Real.exp (r * M.templateSupportExponent v (mode j)),
    vertex, ?_, ?_, ?_, hv0, hvN, ?_, ?_⟩
  · intro j
    exact (hc j).mul_const _
  · intro j
    simpa only [vertex, LinearEquiv.apply_symm_apply, Function.comp_def] using
      e.symm.continuous.measurable.comp (hg j)
  · intro q j
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hampc q j) (Real.exp_pos _).le
  · intro q j
    have hb := hbound (M.templateSupportExponent v) t hst γ hγ r hr
      (word.map (fun z => (z.1, z.2 q)))
      (by simpa only [List.length_map] using hlen) (by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact hamp q w hw) j.val
    obtain ⟨w, hw, hnorm⟩ := hb
    have heq : vertex q j = w := hinj (by
      rw [hEval, hprefix, one_mul]
      exact hw.symm)
    simpa only [heq] using hnorm
  · intro q j
    change E (vertex q j.succ) = E (vertex q j.castSucc) * _
    rw [hEval, hEval, hstep]
    congr 1
    simp only [E, X, smul_smul, Function.comp_apply]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateSupports
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.cartanWeightDilation_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_add_apply _root_.OAI.PolycyclicRecognition.cartanWeightScale_zero_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual supporting Cartan directions for compact height templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Set

set_option maxHeartbeats 1000000 in
/-- All the independently supported generator exponents are realized by
actual Cartan vectors whose heights stay in the given compact template. -/
theorem exists_cartan_template_supports
    {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
    (M : CartanWordModel H) {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) :
    ∃ v : Fin M.letterCount → H,
      (∀ i, eW (heightProjection T.character (v i : L)) ∈ E) ∧
      M.templateSupportExponent v = (M.supportIn T hunimod eW).weightSupport E := by
  classical
  choose w hw hs using fun i => (M.supportIn T hunimod eW).exists_weightSupport_point hE hne i
  let v : Fin M.letterCount → H := fun i => cartanHeightSection T H (eW.symm (w i))
  have hv i : eW (heightProjection T.character (v i : L)) = w i := by simp [v]
  refine ⟨v, fun i => hv i ▸ hw i, ?_⟩
  funext i
  rw [hs i]
  change M.weight i (v i) = cartanHeightWeight T H (M.weight i) (eW.symm (w i))
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasurableBoxChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Borel generator chains for the actual compact probe templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [MeasurableSpace A]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- The compact template supplies its own support directions. Every Borel
sampler in its coordinate box then has a fixed-length generator chain,
with measurable prefixes and uniform bounds in a dominating box. -/
theorem exists_measurable_box_generator_chain
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ r : ℝ, 0 ≤ r → ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ t : Fin M.letterCount → ℝ,
      (∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i) →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ (mode : Fin N → Fin M.letterCount) (coeff : A → Fin N → ℝ)
        (vertex : A → Fin (N + 1) → cartanRootIdeal H),
        (∀ j, Measurable (fun q => coeff q j)) ∧
        (∀ j, Measurable (fun q => b₀.equivFun (vertex q j))) ∧
        (∀ q j, |coeff q j| ≤ C * Real.exp (r *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) ∧
        (∀ q, vertex q 0 = 0) ∧
        (∀ q, vertex q (Fin.last N) = (M.boxBasis T hunimod eW E β r).equivFun.symm (y q).val) ∧
        (∀ q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) r).equivFun (vertex q j)‖ ≤ D) ∧
        ∀ q j, F.ExpN (F.N.equiv (vertex q j.succ)) =
          F.ExpN (F.N.equiv (vertex q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff q j • M.letter (mode j))) := by
  obtain ⟨v, _, hv⟩ := M.exists_cartan_template_supports T hunimod eW E hE hne
  obtain ⟨N, C, D, hC, hD, hchain⟩ := M.exists_measurable_template_generator_chain (A := A) T F
    hExp realize haarN dynkinN b₀ v R hR
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro r hr β γ hβ t hst hγ y hy
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val := by
    change IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent ((M.supportIn T hunimod eW).weightSupport E) w) β.val at hβ
    simpa only [hv] using hβ
  have hst' : ∀ i, M.templateSupportExponent v i ≤ t i := by simpa only [hv] using hst
  have hh := hchain r hr β γ hβ' t hst' hγ y hy
  simpa only [hv, CartanWordModel.boxBasis, CartanWordModel.boxCost] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanProbeChainSequence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform measurable chains for varying probe spaces -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Varying compact probe spaces at every scale use one common chain
length and amplitude bound. The canonical coordinate-ball selector is
chosen once and then composed with each actual Borel probe sampler. -/
theorem exists_measurable_probe_chain_sequence
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (t : Fin M.letterCount → ℝ)
    (hst : ∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (y : ∀ n, Y n → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R)
    (hy : ∀ n, Measurable (y n)) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∃ (mode : ℕ → Fin N → Fin M.letterCount)
        (coeff : ∀ n, Y n → Fin N → ℝ)
        (vertex : ∀ n, Y n → Fin (N + 1) → cartanRootIdeal H),
        (∀ n j, Measurable (fun q => coeff n q j)) ∧
        (∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode n j))) ∧
        (∀ n q, vertex n q 0 = 0) ∧
        (∀ n q, vertex n q (Fin.last N) =
          (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm (y n q).val) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤ D) ∧
        ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n j))) := by
  let Z := closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R
  obtain ⟨N, C, D, hC, hD, hchain⟩ :=
    M.exists_measurable_box_generator_chain (A := Z) T F hunimod eW
      hExp realize haarN dynkinN b₀ E hE hne R hR
  have hn (n : ℕ) := hchain (scale n) (hr n) β γ hβ t hst hγ (fun z : Z => z) measurable_id
  choose mode coeff vertex hc hv ha hz he hb hs using hn
  refine ⟨N, C, D, hC, hD, mode, (fun n q => coeff n (y n q)),
    (fun n q => vertex n (y n q)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n j
    exact (hc n j).comp (hy n)
  · intro n j
    exact (hv n j).comp (hy n)
  · intro n q j
    exact ha n (y n q) j
  · intro n q
    exact hz n (y n q)
  · intro n q
    exact he n (y n q)
  · intro n q j
    exact hb n (y n q) j
  · intro n q j
    exact hs n (y n q) j

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable chains for actual group-valued probes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Actual Borel probe endpoints in the group box admit simultaneous
measurable generator chains. Coordinates are recovered through the
published exponential homeomorphism, so no logarithmic sampler is assumed. -/
theorem exists_actual_box_probe_chains
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (t : Fin M.letterCount → ℝ)
    (hst : ∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier) (hp : ∀ n, Measurable (probe n))
    (hprobe : ∀ n q, probe n q ∈ M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) E β (scale n) R) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∃ (mode : ℕ → Fin N → Fin M.letterCount)
        (coeff : ∀ n, Y n → Fin N → ℝ)
        (vertex : ∀ n, Y n → Fin (N + 1) → cartanRootIdeal H),
        (∀ n j, Measurable (fun q => coeff n q j)) ∧
        (∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j))) ∧
        (∀ n q j, |coeff n q j| ≤ C * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode n j))) ∧
        (∀ n q, vertex n q 0 = 0) ∧
        (∀ n q, F.ExpN (F.N.equiv (vertex n q (Fin.last N))) = probe n q) ∧
        (∀ n q j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun k => bracketWordExponent t (γ.val k)) (scale n)).equivFun (vertex n q j)‖ ≤ D) ∧
        ∀ n q j, F.ExpN (F.N.equiv (vertex n q j.succ)) =
          F.ExpN (F.N.equiv (vertex n q j.castSucc)) *
            F.ExpN (F.N.equiv (coeff n q j • M.letter (mode n j))) := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let coordinates (n : ℕ) : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ≃ₜ F.N.carrier :=
    (((M.boxBasis T hunimod eW E β (scale n)).map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans chart
  have he (n : ℕ) (z : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :
      coordinates n z = F.ExpN (F.N.equiv
        ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm z)) := by
    change chart _ = _
    rw [hchart]
    rfl
  have hbound (n : ℕ) (q : Y n) : ‖(coordinates n).symm (probe n q)‖ ≤ R := by
    obtain ⟨v, hv, hb⟩ := hprobe n q
    have hc : coordinates n ((M.boxBasis T hunimod eW E β (scale n)).equivFun v) =
        probe n q := by
      rw [he, LinearEquiv.symm_apply_apply]
      exact hv
    rw [← hc, Homeomorph.symm_apply_apply]
    exact hb
  let y (n : ℕ) (q : Y n) : closedBall
      (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R :=
    ⟨(coordinates n).symm (probe n q), by simpa only [mem_closedBall_zero_iff] using hbound n q⟩
  have hy (n : ℕ) : Measurable (y n) :=
    ((coordinates n).symm.continuous.measurable.comp (hp n)).subtype_mk
  obtain ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩ :=
    M.exists_measurable_probe_chain_sequence T F hunimod eW hExp realize haarN dynkinN
      b₀ E hE hne R hR β γ hβ t hst hγ scale hr y hy
  refine ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, ?_, hb, hs⟩
  intro n q
  rw [hend]
  exact (he n ((coordinates n).symm (probe n q))).symm.trans
    ((coordinates n).apply_symm_apply (probe n q))

set_option maxHeartbeats 1000000 in
/-- Package the actual chains so the three templates can share their
samplers while retaining their individual fixed lengths. -/
theorem nonempty_boxProbeChains
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (R : ℝ) (hR : 0 ≤ R)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (t : Fin M.letterCount → ℝ)
    (hst : ∀ i, (M.supportIn T hunimod eW).weightSupport E i ≤ t i)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : ∀ n, Y n → F.N.carrier) (hp : ∀ n, Measurable (probe n))
    (hprobe : ∀ n q, probe n q ∈ M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) E β (scale n) R) :
    Nonempty (M.BoxProbeChains T F hunimod eW b₀ E γ t scale probe) := by
  obtain ⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩ :=
    M.exists_actual_box_probe_chains T F hunimod eW hExp realize haarN dynkinN
      b₀ E hE hne R hR β γ hβ t hst hγ scale hr probe hp hprobe
  exact ⟨⟨N, C, D, hC, hD, mode, coeff, vertex, hc, hv, ha, hz, hend, hb, hs⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFixedTiledProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tiled chains retain the quotient section chosen before the small parameter -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
set_option maxHeartbeats 1000000 in
theorem exists_tiled_samplers_from_box
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1)
    (ha : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) (scale n) R)) :
    let U := fun n => M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1
    let Z := closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
    ∃ (index : ∀ n, U n → Fin (tiles n)) (probe : ∀ n, Fin 3 → Z × U n → F.N.carrier),
      (∀ n, Measurable (index n)) ∧ (∀ n j, Measurable (probe n j)) ∧
      (∀ n j y, probe n j y ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (E j) (data.γ j) (scale n) (![data.R₀, 1, R] j)) ∧
      (∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
        (quotientLinearSection (M.coneWordIdeal C) data.bQ data.lift
          (data.bQ.equivFun.symm y.1.val)))) ∧
      (∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))) ∧
      ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val)) := by
  classical
  dsimp only
  have hboxes := data.select
  have hex (n : ℕ) := hboxes (scale n) (hr n) R hR
    (φ n) (k n) (hφ n) (tiles n) (anchor n) (tile n) (hm n) (hd n) (hu n) (ha n) (ht n)
  choose index probe properties using hex
  refine ⟨index, probe, fun n => (properties n).1,
    fun n => (properties n).2.1, fun n => (properties n).2.2.1, fun n => (properties n).2.2.2.1,
    fun n => (properties n).2.2.2.2.1, fun n => (properties n).2.2.2.2.2⟩

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_tiled_probe_values_from_box
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ)
    (hdom : ∀ j i, (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i)
    (hambient : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (fun w => bracketWordExponent t w) ambient.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1)
    (ha : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) (scale n) R)) :
    let U := fun n => M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1
    let Z := closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
    ∃ (index : ∀ n, U n → Fin (tiles n)) (probe : ∀ n, Fin 3 → Z × U n → F.N.carrier),
      (∀ n, Measurable (index n)) ∧ (∀ n j, Measurable (probe n j)) ∧
      (∀ j, Nonempty (M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
        (fun n => probe n j))) ∧
      (∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
        (quotientLinearSection (M.coneWordIdeal C) data.bQ data.lift
          (data.bQ.equivFun.symm y.1.val)))) ∧
      (∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))) ∧
      ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val)) := by
  classical
  dsimp only
  obtain ⟨index, probe, hi, hp, hb, hf, hs, ht⟩ :=
    M.exists_tiled_samplers_from_box T F hunimod eW C ExpI ι bN E β data
      scale hr R hR φ k hφ tiles anchor tile hm hd hu ha ht
  refine ⟨index, probe, hi, hp, ?_, hf, hs, ht⟩
  intro j
  have hrad : 0 ≤ (![data.R₀, 1, R] j) := by
    fin_cases j
    · exact data.radius_nonneg
    · exact zero_le_one
    · exact hR
  exact M.nonempty_boxProbeChains T F hunimod eW hExp realize haarN dynkinN
    bN (E j) (hE j) (hne j) (![data.R₀, 1, R] j) hrad (data.γ j) ambient
    (data.maximizing j) t (hdom j) hambient scale hr (fun n => probe n j)
    (fun n => hp n j) (fun n q => hb n j q)

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_tiled_probe_chains_from_box
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ)
    (hdom : ∀ j i, (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i)
    (hambient : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (fun w => bracketWordExponent t w) ambient.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1)
    (ha : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) (scale n) R)) :
    ∃ D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t
      scale φ ι tiles anchor, D.bQ = data.bQ ∧ D.lift = data.lift := by
  obtain ⟨index, probe, hi, hp, hc, hf, hs, ht⟩ :=
    M.exists_tiled_probe_values_from_box T F hunimod eW C hExp realize haarN dynkinN
      ExpI ι bN E hE hne β data ambient t hdom hambient scale hr R hR φ k hφ
      tiles anchor tile hm hd hu ha ht
  exact ⟨⟨data.bQ, data.lift, index, probe, data.lifts, hi, hp, hc, hf, hs, ht⟩, rfl, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarProbeTemplates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual polar-template widths for the three probe boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem weight_mem_heightConePreimage_iff (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K ↔
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K := Iff.rfl

set_option maxHeartbeats 1000000 in
/-- The support exponents of the normalized probe templates are exactly
the polar widths multiplied by their radii. -/
theorem weightSupport_polar_smul (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weightSupport
      ((fun x : W => c • x) '' conePolarTemplate K) i =
      c * conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_smul K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap hc

set_option maxHeartbeats 1000000 in
theorem polar_width_nonneg (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) :
    0 ≤ conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap :=
  conePolarWidth_nonneg K _

set_option maxHeartbeats 1000000 in
theorem polar_width_zero (K : ProperCone ℝ (StrongDual ℝ W))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K) :
    conePolarWidth K ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap = 0 :=
  conePolarWidth_eq_zero K ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mp hi)

set_option maxHeartbeats 1000000 in
/-- The normalized source templates satisfy every compactness, convexity
and zero-width condition required by the actual three-chain construction. -/
theorem polar_probe_template_properties (K : ProperCone ℝ (StrongDual ℝ W))
    {c : ℝ} (hc : 0 ≤ c) :
    let E := (fun x : W => c • x) '' conePolarTemplate K
    IsCompact E ∧ Convex ℝ E ∧ (0 : W) ∈ E ∧
      (∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i) ∧
      ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ heightConePreimage T eW K →
        (M.supportIn T hunimod eW).weightSupport E i = 0 := by
  dsimp only
  refine ⟨(isCompact_conePolarTemplate K).image (continuous_const.smul continuous_id),
    ?_, ⟨0, zero_mem_conePolarTemplate K, smul_zero c⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, convex_conePolarTemplate K hu hv ha hb hab, ?_⟩
    simp only [smul_add, smul_smul, mul_comm c]
  · intro i
    rw [M.weightSupport_polar_smul T hunimod eW K hc]
    exact mul_nonneg hc (M.polar_width_nonneg T hunimod eW K i)
  · intro i hi
    rw [M.weightSupport_polar_smul T hunimod eW K hc,
      M.polar_width_zero T hunimod eW K i hi, mul_zero]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarFixedSection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.bracketWordDifferential_mul _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar probes with a fixed quotient section -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

local notation "C" => heightConePreimage T eW K

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_polar_tiled_probe_chains_from_box_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN
      (normalizedPolarTemplates K ε) (fun _ => β))
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1)
    (ha₀ : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)) :
    ∃ ambient : M.Bases,
      ∃ D : M.TiledProbeChainData T F hunimod eW C ExpI bN
        (normalizedPolarTemplates K ε) (fun _ => β) ambient
        (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor, D.bQ = data.bQ ∧ D.lift = data.lift := by
  classical
  let E := normalizedPolarTemplates K ε
  let t := fun i => ε * M.polarProbeWidths T hunimod eW K i
  have hrad (j : Fin 3) : 0 ≤ threePolarRadii ε j ∧ threePolarRadii ε j ≤ ε := by
    fin_cases j <;> dsimp [threePolarRadii] <;> constructor <;> linarith
  have hprop (j : Fin 3) := M.polar_probe_template_properties T hunimod eW K (hrad j).1
  have hw (j : Fin 3) : (M.supportIn T hunimod eW).weightSupport (E j) =
      fun i => threePolarRadii ε j * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K (hrad j).1 i
  obtain ⟨ambient, ha⟩ := exists_maximizing_wordBasis M.letter M.wordList bN
    (fun w => bracketWordExponent t w)
  have hdom (j : Fin 3) (i) : (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right (hrad j).2 (M.polar_width_nonneg T hunimod eW K i)
  refine ⟨ambient, ?_⟩
  exact M.exists_tiled_probe_chains_from_box T F hunimod eW C hExp realize haarN dynkinN
    ExpI ι bN E (fun j => (hprop j).1) (fun j => ⟨0, (hprop j).2.2.1⟩)
    (fun _ => β) data ambient t hdom ha scale hr R hR φ k hφ
    tiles anchor tile hm hd hu ha₀ ht

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box_oai.{u_1, u_2, u_3, u_4} := @OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box_oai.{u_1, u_2, u_3, u_4}
