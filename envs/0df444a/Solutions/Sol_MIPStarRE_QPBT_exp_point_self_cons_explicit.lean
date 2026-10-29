-- Prove2me | solution 1 for MIPStarRE.QPBT.exp_point_self_cons_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:37:06.250498+00:00
-- url     : https://prove2.me/submissions/d391e12c-2a34-4877-99ef-483988e74e6d

-- Generated proof for MIPStarRE.QPBT.exp_point_self_cons_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_expPointDist_aaBa_le
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_expPointDist_abBb_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Test/PauliBasisTest.lean. -/
/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are blueprint `def:admissible`,
`def:pauli-question-distribution`, and `def:pauli-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section



















/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/


















































set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Deciding the cardinality unfolds the nested finite sum and product alphabets.
/-- The ordered carrier of the Pauli question graph has `86` edges: its
`26` loops occur once, while its `30` non-loop undirected edges occur in both
orientations. This finite computation supports the explicit quantitative
baseline for `thm:pauli`; the graph itself is unchanged. -/
theorem pauli_edge_card : Fintype.card _root_.MIPStarRE.QPBT.PauliEdge = 86 := by
  decide





































end

end MIPStarRE.QPBT

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





/-! ## Consistency of the unexpanded point measurements -/







-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
open MIPStarRE.QPBT.ProjectiveSetting

/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyPointConsistency

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement), p₁.IsOpposite p₂ →
      ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
        _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ 172 * ε := by
  intro P ε S p₁ p₂ hopp W
  cases p₁ <;> cases p₂ <;> simp only [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at hopp
  · convert _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointDist_aaBa_le S W using 1 <;>
      simp only [_root_.MIPStarRE.QPBT.Placement.side, _root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] <;> ring
  · rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    convert _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointDist_aaBa_le S W using 1 <;>
      simp only [_root_.MIPStarRE.QPBT.Placement.side, _root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] <;> ring
  · rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    convert _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointDist_abBb_le S W using 1 <;>
      simp only [_root_.MIPStarRE.QPBT.Placement.side, _root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] <;> ring
  · convert _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointDist_abBb_le S W using 1 <;>
      simp only [_root_.MIPStarRE.QPBT.Placement.side, _root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] <;> ring
