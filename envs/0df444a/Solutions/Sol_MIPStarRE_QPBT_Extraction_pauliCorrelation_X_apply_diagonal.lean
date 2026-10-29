-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.pauliCorrelation_X_apply_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.459794+00:00
-- url     : https://prove2.me/submissions/ac8912b6-fa68-4fdc-afd6-bb260f4d8735

-- Generated proof for MIPStarRE.QPBT.Extraction.pauliCorrelation_X_apply_diagonal.
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
import Definitions.Def_QPBT_QPBT_Extraction_EPRProjection
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction

/- Source helpers from QPBT/Algebra/PauliTheorems.lean. -/
/-! # Pauli product, commutation, and cancellation identities

The principal results are blueprint `lem:twisted-commutation` and
`lem:cancellation`, from
`references/qpbt-paper/04_preliminaries.tex:1056-1095,1124-1151`. The
general-prime statements use the canonical character `ffChar`; binary
declarations below are separately named QPBT specializations.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum









































































/-- A shift observable is the permutation matrix for addition by its label. -/
theorem tauObservable_X_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    _root_.MIPStarRE.QPBT.tauObservable .X a x y = if x = y + a then 1 else 0 := by
  change (∏ i : ι, if x i = y i + a i then 1 else 0) = _
  rw [Fintype.prod_boole]
  have hsupport : (∀ i, x i = y i + a i) ↔ x = y + a := by
    simpa only [Pi.add_apply] using
      (funext_iff (f := x) (g := y + a)).symm
  simp only [hsupport]











end MIPStarRE.QPBT

/-!
# The EPR projection in Pauli extraction

The product of the averaged, paired X and Z observables is the rank-one
projection onto the EPR vector. This is an algebraic prerequisite for constructing
the auxiliary state in `exists_extractionWitness_ofGlobalPairWitness`.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1725-1742`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT.Extraction

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT.Preliminaries



variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]

theorem solution (x : (ι → K) × (ι → K)) (a : ι → K) :
    _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation .X x (a, a) =
      if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0 := by
  simp only [_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [_root_.MIPStarRE.QPBT.tauObservable_X_apply]
  rw [Finset.sum_eq_single (x.1 - a)]
  · simp [add_sub_cancel, eq_comm]
  · intro u _ hu
    have h : x.1 ≠ a + u := by
      intro h
      apply hu
      rw [h, add_sub_cancel_left]
    simp [h]
  · simp
