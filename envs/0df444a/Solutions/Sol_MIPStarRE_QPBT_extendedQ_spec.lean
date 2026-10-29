-- Prove2me | solution 1 for MIPStarRE.QPBT.extendedQ_spec
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.84123+00:00
-- url     : https://prove2.me/submissions/09ddec63-ef0d-43cc-85d4-d3e931c4f049

-- Generated proof for MIPStarRE.QPBT.extendedQ_spec.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_uniform_affine_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_sum_placed_measurement_products_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness

/- Source helpers from QPBT/Combining/Points.lean. -/
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

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section









/-- Register placement distributes over a filtered outcome sum. -/
private theorem place_finset_sum {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*}
    (s : Finset α) (A : α → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a ∈ s, A a) = ∑ a ∈ s, S.place p (A a) := by
  classical
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]





end


end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/PointsDataProcessing.lean. -/
/-!
# Averaged affine coarse-graining of complete operator families

Uniform scalar coefficients give collision probability `1 / card K` for
distinct pairs over a finite field. Expanding the squared state-dependent
distance therefore proves contraction when the two operator families have
the same total operator. The placement lemmas apply this identity to the
complete point measurements and to both ordered measurement products.

## References

This is the finite-dimensional calculation used for the coarse-graining in
`lem:qld-4-12`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1018`.
The operator-family contraction is a formalization-only auxiliary lemma.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section











/-- Register placement preserves the total of a finite operator family. -/
theorem place_sum {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (A : α → _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a, A a) = ∑ a, S.place p (A a) := by
  classical
  ext i j
  cases p <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

private theorem place_one {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) :
    S.place p (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  cases p <;> simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
  all_goals split_ifs <;> simp_all [Prod.ext_iff]

/-- A complete measurement remains complete after register placement. -/
theorem sum_placed_measurement_eq_one {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p.side)) :
    (∑ a, S.place p (M.effect a)) = 1 := by
  rw [← _root_.MIPStarRE.QPBT.place_sum, M.sum_eq_one, place_one]



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

set_option maxHeartbeats 1600000 in
-- Coarse-graining the joint point POVM expands three large finite consistency sums.

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δ : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δ) :
    (∀ side x z alpha beta,
      _root_.MIPStarRE.QPBT.Measurement.IsProjective (points.extendedQ side x z alpha beta)) ∧
    (∀ p1 p2 : _root_.MIPStarRE.QPBT.Placement, p1.IsOpposite p2 ->
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          ((points.extendedQ p2.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        S.psiHat <= δ) ∧
    (∀ p1 p2 : _root_.MIPStarRE.QPBT.Placement, p1.IsOpposite p2 ->
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .X question.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z question.1.2).effect ab.2))
        S.psiHat <= δ) ∧
    ∀ p1 p2 : _root_.MIPStarRE.QPBT.Placement, p1.IsOpposite p2 ->
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .Z question.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X question.1.1).effect ab.1))
        S.psiHat <= δ := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro side x z alpha beta
    exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (points.projective side x z) _
  · intro p1 p2 hopposite
    let A : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab)
    refine le_trans ?_ (points.self_consistent p1 p2 hopposite)
    have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, place_finset_sum] using h
    · rw [_root_.MIPStarRE.QPBT.sum_placed_measurement_eq_one, _root_.MIPStarRE.QPBT.sum_placed_measurement_eq_one]
  · intro p1 p2 hopposite
    let A : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p2.side .Z xz.2).effect ab.2)
    refine le_trans ?_ (points.consistent_XZ p1 p2 hopposite)
    have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, place_finset_sum] using h
    · rw [_root_.MIPStarRE.QPBT.sum_placed_measurement_eq_one, _root_.MIPStarRE.QPBT.sum_placed_measurement_products_eq_one]
  · intro p1 p2 hopposite
    let A : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)
    let B : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        (_root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) → _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun xz ab => S.place p2
        ((S.pointMeasExp p2.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p2.side .X xz.1).effect ab.1)
    refine le_trans ?_ (points.consistent_ZX p1 p2 hopposite)
    have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_uniform_affine_postprocess_le A B S.psiHat (fun xz => ?_)
    · simpa only [A, B, _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, place_finset_sum] using h
    · rw [_root_.MIPStarRE.QPBT.sum_placed_measurement_eq_one]
      have htotal := _root_.MIPStarRE.QPBT.sum_placed_measurement_products_eq_one S p2
        (S.pointMeasExp p2.side .Z xz.2) (S.pointMeasExp p2.side .X xz.1)
      rw [Fintype.sum_prod_type, Finset.sum_comm] at htotal
      simpa only [B, Fintype.sum_prod_type] using htotal.symm
