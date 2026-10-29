-- Prove2me | solution 1 for MIPStarRE.QPBT.tauDotProj_isProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.581261+00:00
-- url     : https://prove2.me/submissions/ecd8607a-2622-4a56-9bcb-e99342c2c1f6

-- Generated proof for MIPStarRE.QPBT.tauDotProj_isProj.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Extraction foundations

This module defines the register identifications used to pull the Pauli
measurements apart. It retains the distinct local spaces of a
heterogeneous strategy, coarse-grains the generalized Pauli projectors by a
dot product, and records the state and error expressions needed by the later
extraction witness.

The binary phases use the existing `phaseSign`; the fixed field basis remains
the basis stored in `P.model` and is not re-quantified here.

## References

The Pauli dot-product projectors formalize blueprint
`def:tau-dot-product-projector`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The register and state helpers support blueprint `def:tilde-m-measurement`,
`def:v-swap-unitary`, and `lem:qld-unitary`, from paper lines 1429-1435 and
1666-1713.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum



/-! ## Heterogeneous extraction registers -/











open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

















/-! ## Coarse-grained Pauli projectors -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : _root_.MIPStarRE.QPBT.PauliRegister P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.tauDotProj W u a) := by
  classical
  let basisMatrix : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P) := fun row label => _root_.MIPStarRE.QPBT.pauliVec W label row
  have hbasisMatrix_conjTranspose (label row : _root_.MIPStarRE.QPBT.PauliRegister P) :
      basisMatrixᴴ label row = star (_root_.MIPStarRE.QPBT.pauliVec W label row) := by
    rfl
  have hbasis : basisMatrix * basisMatrixᴴ = 1 := by
    calc
      basisMatrix * basisMatrixᴴ = ∑ label : _root_.MIPStarRE.QPBT.PauliRegister P, _root_.MIPStarRE.QPBT.pauliProj W label := by
        ext row column
        rw [Matrix.mul_apply]
        simp only [basisMatrix, hbasisMatrix_conjTranspose, _root_.MIPStarRE.QPBT.pauliProj,
          Matrix.sum_apply, Matrix.vecMulVec_apply]
      _ = 1 := _root_.MIPStarRE.QPBT.sum_pauliProj_eq_one W
  let diagonalProj : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P) :=
    Matrix.diagonal (fun label => if dotProduct label u = a then (1 : ℂ) else 0)
  have hdiagonal : _root_.LIDT.MIPStarRE.Quantum.IsProj diagonalProj := by
    constructor
    · change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext label
      split_ifs <;> simp
    · change diagonalProjᴴ = diagonalProj
      simp [diagonalProj, Matrix.diagonal_conjTranspose]
  have hcoarse : _root_.MIPStarRE.QPBT.tauDotProj W u a = basisMatrix * diagonalProj * basisMatrixᴴ := by
    ext row column
    simp only [_root_.MIPStarRE.QPBT.tauDotProj, _root_.MIPStarRE.QPBT.bracketOp, Matrix.sum_apply, _root_.MIPStarRE.QPBT.pauliProj, Matrix.vecMulVec_apply]
    rw [Matrix.mul_apply]
    simp only [diagonalProj, Matrix.mul_diagonal]
    simp [basisMatrix, hbasisMatrix_conjTranspose, Finset.sum_filter, mul_ite, ite_mul]
  rw [hcoarse]
  exact hdiagonal.map (Unitary.conjStarAlgAut ℂ (_root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))
    ⟨basisMatrix, Matrix.mem_unitaryGroup_iff.mpr hbasis⟩)
