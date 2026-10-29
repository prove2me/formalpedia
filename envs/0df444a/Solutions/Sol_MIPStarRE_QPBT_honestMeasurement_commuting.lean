-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMeasurement_commuting
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:24.666795+00:00
-- url     : https://prove2.me/submissions/3bb5e914-1b05-4352-b700-0af6c59e9ab5

-- Generated proof for MIPStarRE.QPBT.honestMeasurement_commuting.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_Completeness_Commutation
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_ms_commute
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_commute_of_oriented
import Theorems.Thm_MIPStarRE_QPBT_pauliEdges_cases
import Theorems.Thm_MIPStarRE_QPBT_pauliQuestionDistribution_pos_incidence

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/HonestStrategy/MeasurementFamily.lean. -/
/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ### Tensor placement and relabeling -/

































/-! ### The total honest measurement family -/







































/-- The effects of one honest measurement commute with one another; this is the
commutation along the self-loops of the Pauli question graph in
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1372`. -/
theorem honestMeasurement_self_commute (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P t z).effect a)
      ((_root_.MIPStarRE.QPBT.honestMeasurement P t z).effect b) := by
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  · rw [commute_iff_eq,
      _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (_root_.MIPStarRE.QPBT.honestMeasurement_projective P t z) hab,
      _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (_root_.MIPStarRE.QPBT.honestMeasurement_projective P t z) (Ne.symm hab)]

end

end MIPStarRE.QPBT

/-!
# Commutation of the honest Pauli measurements

This module proves that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` has commuting effects
on every question pair of positive weight for the Pauli question sampler.  The
argument first characterises the supported question pairs as the typed
conditionally linear images of a single ambient coefficient vector along an edge
of the Pauli type graph, and then treats the five edge families of that graph.

## References

This is the commutation obligation in the proof of `lem:pauli-completeness`,
blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### The supported question pairs -/







/-! ### Coarse-graining and tensor placement -/













/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/







/-! ### Commutation along the Pauli type graph -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    _root_.MIPStarRE.QPBT.IsCommutingOn (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P)
      (fun q : _root_.MIPStarRE.QPBT.PauliQuestion P => _root_.MIPStarRE.QPBT.honestMeasurement P q.1 q.2)
      (fun q : _root_.MIPStarRE.QPBT.PauliQuestion P => _root_.MIPStarRE.QPBT.honestMeasurement P q.1 q.2) := by
  intro x y hxy a b
  obtain ⟨z, hedge, hx, hy⟩ := _root_.MIPStarRE.QPBT.pauliQuestionDistribution_pos_incidence P x y hxy
  change Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P x.1 x.2).effect a)
    ((_root_.MIPStarRE.QPBT.honestMeasurement P y.1 y.2).effect b)
  rw [hx, hy]
  rcases _root_.MIPStarRE.QPBT.pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq]
    exact _root_.MIPStarRE.QPBT.honestMeasurement_self_commute P y.1 _ a b
  · rw [hs₁, hs₂]
    exact _root_.MIPStarRE.QPBT.honestMagicMeasurement_ms_commute P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hms a b
  · exact _root_.MIPStarRE.QPBT.honestMeasurement_commute_of_oriented P hor z a b
  · exact (_root_.MIPStarRE.QPBT.honestMeasurement_commute_of_oriented P hor z b a).symm
