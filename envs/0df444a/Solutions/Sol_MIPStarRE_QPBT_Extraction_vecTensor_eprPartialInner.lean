-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.vecTensor_eprPartialInner
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.465163+00:00
-- url     : https://prove2.me/submissions/2512b09f-0117-4c83-aeb2-a83718003293

-- Generated proof for MIPStarRE.QPBT.Extraction.vecTensor_eprPartialInner.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_EPRState
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Mathlib

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# The auxiliary vector from the EPR projection

Taking the partial inner product with the EPR vector constructs the
unnormalized auxiliary vector. Tensoring it with EPR gives exactly the
orthogonal projection of the original vector onto the EPR subspace.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1769-1783`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum





open MIPStarRE.QPBT.Extraction

theorem solution {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (ψ : EuclideanSpace ℂ (R × (V × V))) :
    _root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.Extraction.eprPartialInner ψ) (_root_.MIPStarRE.QPBT.eprState V) =
      _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState V x)
          (fun y => star (_root_.MIPStarRE.QPBT.eprState V y)))) ψ := by
  ext x
  change (∑ p : V × V, star (_root_.MIPStarRE.QPBT.eprState V p) * ψ (x.1, p)) * _root_.MIPStarRE.QPBT.eprState V x.2 =
    ∑ j : R × (V × V),
      ((1 : _root_.LIDT.MIPStarRE.Quantum.Op R) x.1 j.1 * (_root_.MIPStarRE.QPBT.eprState V x.2 * star (_root_.MIPStarRE.QPBT.eprState V j.2))) * ψ j
  conv_rhs => rw [Fintype.sum_prod_type]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring
