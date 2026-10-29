-- Prove2me | solution 1 for MIPStarRE.QPBT.applyOperatorToState_heteroKron_vecTensor
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:44.965341+00:00
-- url     : https://prove2.me/submissions/56c96062-6a33-468e-815b-a00b188a9281

-- Generated proof for MIPStarRE.QPBT.applyOperatorToState_heteroKron_vecTensor.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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



-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Coordinate tensors -/

theorem solution {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ι) (B : _root_.LIDT.MIPStarRE.Quantum.Op κ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron A B) (_root_.MIPStarRE.QPBT.vecTensor u v) =
      _root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.applyOperatorToState A u) (_root_.MIPStarRE.QPBT.applyOperatorToState B v) := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  change (Matrix.mulVec (_root_.MIPStarRE.QPBT.heteroKron A B) (_root_.MIPStarRE.QPBT.vecTensor u v).ofLp) (i, j) =
    (Matrix.mulVec A u.ofLp) i * (Matrix.mulVec B v.ofLp) j
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec,
    Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  change _root_.MIPStarRE.QPBT.heteroKron A B (i, j) (k, l) * (_root_.MIPStarRE.QPBT.vecTensor u v).ofLp (k, l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  change A i k * B j l * (u.ofLp k * v.ofLp l) =
    A i k * u.ofLp k * (B j l * v.ofLp l)
  ring
