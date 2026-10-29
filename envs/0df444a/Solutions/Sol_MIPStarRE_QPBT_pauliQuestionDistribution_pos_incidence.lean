-- Prove2me | solution 1 for MIPStarRE.QPBT.pauliQuestionDistribution_pos_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:54.052208+00:00
-- url     : https://prove2.me/submissions/b9ee44b6-aec3-45c8-8cdf-7b6cc6e6dcf7

-- Generated proof for MIPStarRE.QPBT.pauliQuestionDistribution_pos_incidence.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (x y : _root_.MIPStarRE.QPBT.PauliQuestion P) (hxy : 0 < (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P).weight (x, y)) :
    ∃ z : _root_.MIPStarRE.QPBT.PauliSpace P, Sym2.mk x.1 y.1 ∈ _root_.MIPStarRE.QPBT.pauliEdges ∧
      x.2 = _root_.MIPStarRE.QPBT.pauliCL P x.1 z ∧ y.2 = _root_.MIPStarRE.QPBT.pauliCL P y.1 z := by
  classical
  letI : Nonempty _root_.MIPStarRE.QPBT.PauliEdge := _root_.MIPStarRE.QPBT.pauliEdge_nonempty
  set F : _root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P → _root_.MIPStarRE.QPBT.PauliQuestion P × _root_.MIPStarRE.QPBT.PauliQuestion P :=
    fun q => ((q.1.val.1, _root_.MIPStarRE.QPBT.pauliCL P q.1.val.1 q.2),
      (q.1.val.2, _root_.MIPStarRE.QPBT.pauliCL P q.1.val.2 q.2)) with hF
  have hEq : _root_.MIPStarRE.QPBT.pauliQuestionDistribution P =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P)).map F := rfl
  rw [hEq] at hxy
  have hmem : (x, y) ∈
      ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P)).map F).support := by
    by_contra hnot
    rw [((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliEdge × _root_.MIPStarRE.QPBT.PauliSpace P)).map F).outsideSupport _ hnot]
      at hxy
    exact lt_irrefl 0 hxy
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_support, _root_.LIDT.MIPStarRE.LDT.uniformDistribution_support] at hmem
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hmem
  have hx : x = (q.1.val.1, _root_.MIPStarRE.QPBT.pauliCL P q.1.val.1 q.2) := (congrArg Prod.fst hq).symm
  have hy : y = (q.1.val.2, _root_.MIPStarRE.QPBT.pauliCL P q.1.val.2 q.2) := (congrArg Prod.snd hq).symm
  subst hx
  subst hy
  exact ⟨q.2, q.1.2, rfl, rfl⟩
