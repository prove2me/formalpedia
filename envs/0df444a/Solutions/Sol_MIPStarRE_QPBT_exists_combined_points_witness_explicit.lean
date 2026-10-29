-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_combined_points_witness_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:32:41.255527+00:00
-- url     : https://prove2.me/submissions/e8cb87fd-689a-4b7c-b160-027bbc974df8

-- Generated proof for MIPStarRE.QPBT.exists_combined_points_witness_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_Combining_Points_Consistency
import Definitions.Def_QPBT_QPBT_Combining_Points_Orthonormalization
import Definitions.Def_QPBT_QPBT_Combining_Points_Placement
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Points_Sandwich
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_sum_norm_sub_apply_sq_le_four
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_avg_sandwich_defect_bound_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_chain_bounds
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_exists_projective_close_sandwich
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_exp_point_comm_explicit
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_ordered_cross_dist_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_error_terms_le_rpow_eighth
import Theorems.Thm_MIPStarRE_QPBT_sum_mul_conjTranspose_mul_self_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/Points/Closeness.lean. -/
/-!
# Closeness estimates for the combined point measurements

Given projective measurements `Q^{x,z}` on each player's expanded local space
that are close to the sandwich POVMs on the placements where they were
constructed, this file assembles the three conclusions of `lem:qld-4-10` on
every pair of opposite placements by the triangle inequality along
`Q ≈ R ≈ M^Z M^X ≈ M^X M^Z` and the cross-placement consistency of the
ordered products.  It also records the bound `4` on the averaged squared
state-dependent distance of two families satisfying `∑ a, (A a)ᴴ * A a ≤ 1`
and `∑ a, (B a)ᴴ * B a ≤ 1` at every question, used when the test error
exceeds one, and the elementary estimate collapsing the error terms `ε`,
`√ε`, and `(ε + √ε)^{1/4}` into a single power `ε^{1/8}` when `ε ≤ 1`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:838-881`
(self-consistency and consistency with `M̂` in the proof of `lem:qld-4-10`),
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:803-960`; the route
is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## The trivial bound -/



/-- The averaged squared state-dependent distance of two families is at most
`4` on a unit vector, under a uniform distribution, provided the sums
`∑ a, (A x a)ᴴ * A x a` and `∑ a, (B x a)ᴴ * B x a` are at most the identity
for every question `x`. -/
theorem opFamilyDistSq_uniform_le_four {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype α] [Fintype ι] [DecidableEq ι]
    (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, ∑ a, (A x a)ᴴ * A x a ≤ 1) (hB : ∀ x, ∑ a, (B x a)ᴴ * B x a ≤ 1) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) A B ψ ≤ 4 := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  calc _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x =>
        ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun _ => (4 : ℝ)) := by
        refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun x => ?_
        exact _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_sub_apply_sq_le_four (A x) (B x) ψ hψ (hA x) (hB x)
    _ = 4 := _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const _



/-- The products `B_b A_a` of the effects of two projective measurements on a
common space, indexed by the pair `(a, b)`, satisfy
`∑ a b, (B_b A_a)ᴴ * (B_b A_a) = 1`. -/
theorem sum_mul_conjTranspose_mul_self_eq_one' {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : _root_.MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (B.effect ab.2 * A.effect ab.1)ᴴ * (B.effect ab.2 * A.effect ab.1) =
      1 := by
  have h := _root_.MIPStarRE.QPBT.sum_mul_conjTranspose_mul_self_eq_one B A hB hA
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa only [Fintype.sum_prod_type] using h

/-! ## The chain of closeness estimates -/



/-! ## Collapsing the error terms into one power -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/Consistency.lean. -/
/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Quadratic-form identities -/









/-! ## The overlap of two placed sandwiches -/



/-! ## The bound for the placed sandwiches -/

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}



/-- The pointwise bound is nonnegative. -/
theorem sandwichDefectBound_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement)
    (xz : _root_.MIPStarRE.QPBT.PointPair P) : 0 ≤ S.sandwichDefectBound p₁ p₂ xz := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichDefectBound
  positivity







end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/Orthonormalization.lean. -/
/-!
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Jensen's inequality for the fourth root -/





/-! ## The bipartition with Bob's registers first -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- Under the `BA'' | AA'(B'B'')` bipartition, a `BA''` placement is the
ordinary left tensor placement. -/
theorem reindexOp_baAaBipartition_left (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace _root_.MIPStarRE.QPBT.Placement.BA''.side)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.heteroKron O
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
      S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.baAaBipartition, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-- Under the `BA'' | AA'(B'B'')` bipartition, an `AA'` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_baAaBipartition_right (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace _root_.MIPStarRE.QPBT.Placement.AA'.side)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron O (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
      S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.baAaBipartition, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-! ## Transport along a bipartition -/



/-- Fiberwise orthonormalization on Alice's side, for the placement pair
`AA'`, `BA''`.  Both the pointwise and the averaged bound are on squared
distances. -/
theorem exists_projective_close_sandwich_alice (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    ∃ Q : _root_.MIPStarRE.QPBT.PointPair P →
        _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) (S.ExpandedLocalSpace .alice),
      (∀ xz, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q xz)) ∧
        (∀ xz, ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (S.place .AA' ((Q xz).effect ab) -
              S.place .AA' ((S.sandwichPoint .alice xz.1 xz.2).effect ab))
            S.psiHat‖ ^ 2 ≤
            220 * Real.rpow (S.sandwichDefectBound .AA' .BA'' xz) (1 / 4 : ℝ)) ∧
        _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
          (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
            S.place .AA' ((Q xz).effect ab))
          (fun xz ab => S.place .AA' ((S.sandwichPoint .alice xz.1 xz.2).effect ab))
          S.psiHat ≤
          220 * Real.rpow (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
            (S.sandwichDefectBound .AA' .BA'')) (1 / 4 : ℝ) :=
  S.exists_projective_close_sandwich .AA' .BA'' trivial
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (fun O => _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left S O)
    (fun O => _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right S O)

/-- Fiberwise orthonormalization on Bob's side, for the placement pair
`BA''`, `AA'`.  Both the pointwise and the averaged bound are on squared
distances. -/
theorem exists_projective_close_sandwich_bob (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    ∃ Q : _root_.MIPStarRE.QPBT.PointPair P →
        _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) (S.ExpandedLocalSpace .bob),
      (∀ xz, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q xz)) ∧
        (∀ xz, ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (S.place .BA'' ((Q xz).effect ab) -
              S.place .BA'' ((S.sandwichPoint .bob xz.1 xz.2).effect ab))
            S.psiHat‖ ^ 2 ≤
            220 * Real.rpow (S.sandwichDefectBound .BA'' .AA' xz) (1 / 4 : ℝ)) ∧
        _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
          (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
            S.place .BA'' ((Q xz).effect ab))
          (fun xz ab => S.place .BA'' ((S.sandwichPoint .bob xz.1 xz.2).effect ab))
          S.psiHat ≤
          220 * Real.rpow (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
            (S.sandwichDefectBound .BA'' .AA')) (1 / 4 : ℝ) :=
  S.exists_projective_close_sandwich .BA'' .AA' trivial
    (_root_.MIPStarRE.QPBT.baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (fun O => _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_baAaBipartition_left S O)
    (fun O => _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_baAaBipartition_right S O)

end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective









































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

















































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/



/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_sub (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    (O₁ O₂ : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.sub_apply, sub_mul, mul_sub]

/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/







/-- Coordinates of an operator applied to a reindexed state. Formalization-only
support for the interchanged conclusions of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem applyOperatorToState_reindexState_ofLp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) (k : κ) :
    (_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)).ofLp k =
      (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp (e.symm k) := by
  change (T *ᵥ (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp) k = (_root_.MIPStarRE.QPBT.reindexOp e T *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← e.sum_comp (fun l : κ => T k l * (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp l)]
  apply Finset.sum_congr rfl
  intro j _
  simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.reindexOp]

/-- Reindexing a state and its operator preserves the length of the image.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem norm_applyOperatorToState_reindexState {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← e.symm.sum_comp (fun i : ι =>
      ‖(_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_reindexState_ofLp]







/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/













/-! ## Numeric bookkeeping -/





end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/



















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h















/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Combining/Points/Placement.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
EPR exchange is a distinct auxiliary permutation, not the product `U_σ U_θ`
of `lem:symmetric-equivalents-transfer` in that blueprint.  It supports
transfer between the two bipartition schemes without symmetry of the strategy;
its use for `lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The crosswise exchange of the two EPR pairs -/



/-- The EPR vector is symmetric in its two registers. -/
theorem eprState_ofLp_swap {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (x y : V) :
    (_root_.MIPStarRE.QPBT.eprState V).ofLp (x, y) = (_root_.MIPStarRE.QPBT.eprState V).ofLp (y, x) := by
  change (if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0) =
    (if y = x then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The auxiliary crosswise EPR exchange fixes the expanded state.  Only the
symmetry of the EPR vector is used; no symmetry of the strategy is needed. -/
theorem reindexState_eprCrossSwap_psiHat (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat =
      S.psiHat := by
  ext i
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  change S.toStrategy.ψ.ofLp (a, b) * (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)).ofLp (b'', b') *
      (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)).ofLp (a'', a') =
    S.toStrategy.ψ.ofLp (a, b) * (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)).ofLp (a', a'') *
      (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)).ofLp (b', b'')
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.eprState_ofLp_swap b'' b', _root_.MIPStarRE.QPBT.ProjectiveSetting.eprState_ofLp_swap a'' a']
  ring

/-- The crosswise EPR exchange carries the `AB''` placement to the `AA'`
placement. -/
theorem reindexOp_eprCrossSwap_place_AB'' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.ProjectiveSetting.eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .AB'' O) = S.place .AA' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.ProjectiveSetting.eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- The crosswise EPR exchange carries the `BB'` placement to the `BA''`
placement. -/
theorem reindexOp_eprCrossSwap_place_BB' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.ProjectiveSetting.eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB)
      (S.place .BB' O) = S.place .BA'' O := by
  ext i j
  obtain ⟨⟨a, a', a''⟩, b, b', b''⟩ := i
  obtain ⟨⟨c, c', c''⟩, d, d', d''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.ProjectiveSetting.eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
  ring!

/-- An operator placed on `AB''` has, on the expanded state, the same norm as
the same operator placed on `AA'`.  The auxiliary crosswise EPR exchange
gives this transfer without assuming a symmetric strategy. -/
theorem norm_place_AB''_eq_norm_place_AA' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .AB'' O) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .AA' O) S.psiHat‖ := by
  conv_lhs => rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexState_eprCrossSwap_psiHat S]
  rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_eprCrossSwap_place_AB'']

/-- An operator placed on `BB'` has, on the expanded state, the same norm as
the same operator placed on `BA''`.  The auxiliary crosswise EPR exchange
gives this transfer without assuming a symmetric strategy. -/
theorem norm_place_BB'_eq_norm_place_BA'' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .BB' O) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .BA'' O) S.psiHat‖ := by
  conv_lhs => rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexState_eprCrossSwap_psiHat S]
  rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_eprCrossSwap_place_BB']

/-- Transfer of a same-side state-dependent distance between the `AA'` and
`AB''` placements. -/
theorem opFamilyDistSq_place_AB''_eq_AA' {X α : Type*} [Fintype α]
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => S.place .AB'' (A x a))
        (fun x a => S.place .AB'' (B x a)) S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => S.place .AA' (A x a))
        (fun x a => S.place .AA' (B x a)) S.psiHat := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AB''_eq_norm_place_AA']
  all_goals rfl

/-- Transfer of a same-side state-dependent distance between the `BA''` and
`BB'` placements. -/
theorem opFamilyDistSq_place_BB'_eq_BA'' {X α : Type*} [Fintype α]
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => S.place .BB' (A x a))
        (fun x a => S.place .BB' (B x a)) S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => S.place .BA'' (A x a))
        (fun x a => S.place .BA'' (B x a)) S.psiHat := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_BB'_eq_norm_place_BA'']
  all_goals rfl

end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/













/-! ## The placement is a unital `*`-homomorphism -/











/-- The placement of a local operator bounded by the identity is bounded by
the identity. -/
theorem place_le_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement)
    {A : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)} (hA : A ≤ 1) :
    S.place p A ≤ 1 := by
  have h : 0 ≤ S.place p (1 - A) := S.place_nonneg p (sub_nonneg.mpr hA)
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_one] at h
  exact sub_nonneg.mp h

/-- The placement of a projector is a contraction. -/
theorem place_conjTranspose_mul_self_le_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) {E : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)} (hE : _root_.LIDT.MIPStarRE.Quantum.IsProj E) :
    (S.place p E)ᴴ * S.place p E ≤ 1 := by
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, hE.isSelfAdjoint.isHermitian.eq,
    hE.isIdempotentElem.eq]
  exact S.place_le_one p (sub_nonneg.mp hE.one_sub.nonneg)







/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p.side))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := by
  intro a
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p (M.effect a) * S.place p (M.effect a) =
      S.place p (M.effect a)
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, (hM a).isIdempotentElem.eq]
  · change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose,
      (hM a).isSelfAdjoint.isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems.lean. -/
/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus











/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one























end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Points/Sandwich.lean. -/
/-!
# The sandwich POVM of the expanded point measurements

The first step of the proof of `lem:qld-4-10` combines the two expanded point
measurements into the sandwich POVM
`R^{x,z}_{a,b} = M^{(Point,Z),z}_b M^{(Point,X),x}_a M^{(Point,Z),z}_b`.  The
source forms it from the binary refinements; here it is formed directly with
outcomes in `F_q × F_q`, which the Parseval transfer of
`MIPStarRE/QPBT/Combining/Points/Commutation.lean` makes possible.  This file
defines the POVM, proves that it is close to the ordered product
`M^Z_b M^X_a` by the approximate commutation, and records the consistency of
the ordered products across opposite register placements, which follows from
the self-consistency of each factor.

## Main results

* `ProjectiveSetting.sandwichPoint`: the sandwich POVM.
* `sandwichPoint_ordered_dist_le`: closeness of the sandwich to the ordered
  product on every placement, with the error of `lem:qld-comm-cons`.
* `ordered_cross_dist_le`: the ordered product on one placement is close to
  the reversed ordered product on the opposite placement.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:731-748`
(the sandwich and display `eq:qld-r-2`), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:803-960` (`lem:qld-4-10`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}













/-- The sandwich differs from the ordered product `M^Z_b M^X_a` by
`M^Z_b` times the commutator.  This is the algebra behind display
`eq:qld-r-2`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:737-742`. -/
theorem sandwichPoint_effect_sub_ordered (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.sandwichPoint side x z).effect ab -
        (S.pointMeasExp side .Z z).effect ab.2 *
          (S.pointMeasExp side .X x).effect ab.1 =
      (S.pointMeasExp side .Z z).effect ab.2 *
        ((S.pointMeasExp side .X x).effect ab.1 *
            (S.pointMeasExp side .Z z).effect ab.2 -
          (S.pointMeasExp side .Z z).effect ab.2 *
            (S.pointMeasExp side .X x).effect ab.1) := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichPoint_effect, mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp_effect_mul_self]

/-- The sandwich POVM is close to the ordered product `M^Z_b M^X_a` on every
register placement, on average over the point pair, with the error of
`lem:qld-comm-cons`.  This is display `eq:qld-r-2` of the proof of
`lem:qld-4-10`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:737-742`, with
field-valued outcomes. -/
theorem sandwich_point_ordered_dist_le_explicit :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p : _root_.MIPStarRE.QPBT.Placement),
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p
          ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p.side .X xz.1).effect ab.1))
        S.psiHat ≤ _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant * Real.sqrt ε := by
  intro P ε S p
  refine le_trans ?_ (_root_.MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit P ε S p)
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun xz => Finset.sum_le_sum fun ab _ => ?_
  rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichPoint_effect_sub_ordered, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul,
    _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_sub]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
      (S.place_conjTranspose_mul_self_le_one p
        (S.pointMeasExp_isProjective p.side .Z xz.2 ab.2)) _) 2







end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Combining the point measurements

This module constructs the projective joint X/Z point measurements and defines
their scalar linear coarse-graining. The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





open MIPStarRE.QPBT.CombinedPointsWitness

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
      Nonempty (_root_.MIPStarRE.QPBT.CombinedPointsWitness S
        (_root_.MIPStarRE.QPBT.pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ))) := by
  intro P ε S
  let C₀ : ℝ := 344 + 3 * _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant
  let C₁ : ℝ := _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant
  let C₂ : ℝ := _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant
  let C₃ : ℝ := 688
  have hC₀ : (1 : ℝ) ≤ C₀ := by
    dsimp [C₀, _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant, _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  have hC₁ : (1 : ℝ) ≤ C₁ := by
    dsimp [C₁, _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant, _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  have hC₂ : (1 : ℝ) ≤ C₂ := by simpa only [C₂] using hC₁
  have hC₃ : (1 : ℝ) ≤ C₃ := by norm_num [C₃]
  have h₀ := _root_.MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit
  have h₁ := _root_.MIPStarRE.QPBT.ProjectiveSetting.sandwich_point_ordered_dist_le_explicit
  have h₂ := _root_.MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit
  have h₃ := _root_.MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit
  -- the universal constant of the final error `K ε^{1/8}`
  set K : ℝ := _root_.MIPStarRE.QPBT.pauliBaselinePointConstant with hK
  have hKformula : K =
      12 * (440 * (2 * C₀)) + 20 * C₁ + 16 * C₃ + 4 * C₂ := by
    rw [hK]
    dsimp [C₀, C₁, C₂, C₃]
    unfold _root_.MIPStarRE.QPBT.pauliBaselinePointConstant
    ring
  have hK4 : (4 : ℝ) ≤ K := by rw [hKformula]; nlinarith
  have hε : (0 : ℝ) ≤ ε := by
    have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  obtain ⟨Qa, hQa, -, hQaR⟩ := S.exists_projective_close_sandwich_alice
  obtain ⟨Qb, hQb, -, hQbR⟩ := S.exists_projective_close_sandwich_bob
  -- the joint measurements on the two sides
  let Q : (side : _root_.MIPStarRE.QPBT.PlayerSide) → _root_.MIPStarRE.QPBT.PointPair P →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) (S.ExpandedLocalSpace side) :=
    fun side => match side with
      | .alice => Qa
      | .bob => Qb
  have hQproj : ∀ side xz, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q side xz) := by
    intro side xz
    cases side
    · exact hQa xz
    · exact hQb xz
  -- the closeness of `Q` to the sandwich on every placement
  set η : ℝ := 440 * Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) with hη
  have hbound : ∀ p₁ p₂ : _root_.MIPStarRE.QPBT.Placement, p₁.IsOpposite p₂ →
      220 * Real.rpow (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤ η := by
    intro p₁ p₂ hopp
    have hnn : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (S.sandwichDefectBound p₁ p₂) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ (S.sandwichDefectBound_nonneg p₁ p₂)
    have hr : Real.rpow (_root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤
        Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hnn (by simpa only [C₀] using h₀ P ε S p₁ p₂ hopp)
        (by norm_num)
    have hr0 : 0 ≤ Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    rw [hη]
    nlinarith
  have hQR : ∀ p : _root_.MIPStarRE.QPBT.Placement, _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ η := by
    intro p
    cases p
    · exact le_trans hQaR (hbound .AA' .BA'' trivial)
    · exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_place_BB'_eq_BA'']
      exact le_trans hQbR (hbound .BA'' .AA' trivial)
    · rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.opFamilyDistSq_place_AB''_eq_AA']
      exact le_trans hQaR (hbound .AA' .BA'' trivial)
  have hchain := fun (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂) =>
    S.chain_bounds Q η C₁ C₂ C₃ hQR
      (by simpa only [C₁] using h₁ P ε S)
      (by simpa only [C₂] using h₂ P ε S)
      (by simpa only [C₃] using h₃ P ε S) p₁ p₂ hopp
  -- the numeric bound on the longest chain, in the two regimes of `ε`
  have hηnn : 0 ≤ η := by
    rw [hη]
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (mul_nonneg (by linarith) (add_nonneg hε (Real.sqrt_nonneg ε))) _)
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have htotal : 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) +
      4 * (C₂ * Real.sqrt ε) ≤ K * Real.rpow ε (1 / 8 : ℝ) ∨ 1 < ε := by
    by_cases hε1 : ε ≤ 1
    · left
      obtain ⟨hε8, hs8, hq8⟩ := _root_.MIPStarRE.QPBT.error_terms_le_rpow_eighth hε hε1 hC₀
      rw [hη, hKformula]
      nlinarith [mul_le_mul_of_nonneg_left hq8 (by norm_num : (0 : ℝ) ≤ 440),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₁),
        mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ C₂),
        mul_le_mul_of_nonneg_left hε8 (by linarith : (0 : ℝ) ≤ C₃)]
    · right
      exact lt_of_not_ge hε1
  have hK8 : 1 < ε → (4 : ℝ) ≤ K * Real.rpow ε (1 / 8 : ℝ) := by
    intro hε1
    have h1 : (1 : ℝ) ≤ Real.rpow ε (1 / 8 : ℝ) :=
      Real.one_le_rpow (le_of_lt hε1) (by norm_num)
    nlinarith
  have hsub1 : 2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  have hsub2 : 4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) +
      2 * (C₂ * Real.sqrt ε) ≤
      12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₂ * Real.sqrt ε) := by
    nlinarith
  -- square-summability of the families, for the trivial bound
  have hsqQ : ∀ (p : _root_.MIPStarRE.QPBT.Placement) (xz : _root_.MIPStarRE.QPBT.PointPair P),
      (∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        (S.place p ((Q p.side xz).effect ab))ᴴ *
          S.place p ((Q p.side xz).effect ab)) ≤ 1 :=
    fun p xz => _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (S.placedMeasurement p (Q p.side xz))
  have hsqXZ : ∀ (p : _root_.MIPStarRE.QPBT.Placement) (xz : _root_.MIPStarRE.QPBT.PointPair P),
      (∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))ᴴ *
        S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2)) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul]
    exact _root_.MIPStarRE.QPBT.sum_mul_conjTranspose_mul_self_eq_one
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  have hsqZX : ∀ (p : _root_.MIPStarRE.QPBT.Placement) (xz : _root_.MIPStarRE.QPBT.PointPair P),
      (∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))ᴴ *
        S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1)) ≤ 1 := by
    intro p xz
    refine le_of_eq ?_
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul]
    exact _root_.MIPStarRE.QPBT.sum_mul_conjTranspose_mul_self_eq_one'
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
  refine ⟨_root_.MIPStarRE.QPBT.CombinedPointsWitness.mk (fun side x z => Q side (x, z)) ?_ ?_ ?_ ?_⟩
  · intro side x z
    exact hQproj side (x, z)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.2 htot
    · exact le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqQ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).1 (le_trans hsub1 htot)
    · exact le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqXZ p₂ xz)) (hK8 hε1)
  · intro p₁ p₂ hopp
    rcases htotal with htot | hε1
    · exact le_trans (hchain p₁ p₂ hopp).2.1 (le_trans hsub2 htot)
    · exact le_trans (_root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (fun xz => hsqQ p₁ xz) (fun xz => hsqZX p₂ xz)) (hK8 hε1)
