-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.pauliCorrelation_mul_eq_epr
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.374343+00:00
-- url     : https://prove2.me/submissions/85f4d4ab-69b2-4f17-92cb-f3b2d93990ba

-- Generated proof for MIPStarRE.QPBT.Extraction.pauliCorrelation_mul_eq_epr.
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
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Extraction_pauliCorrelation_X_apply_diagonal
import Theorems.Thm_MIPStarRE_QPBT_Extraction_pauliCorrelation_Z_apply

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction

/- Source helpers from QPBT/Algebra/Pauli.lean. -/
/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]























/-- Conjugated form of `inv_sqrt_natCast_mul_self`: the normalizing amplitude
`(√n)⁻¹` is real, so pairing it with its conjugate again gives `n⁻¹`.  This
formalization-only auxiliary is the form in which the identity occurs in Born
amplitudes, where the bra side carries the conjugate. -/
theorem inv_sqrt_natCast_mul_conj (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (n : ℂ)⁻¹ := by
  rw [show (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (n : ℝ) : ℂ)⁻¹ by simp]
  exact _root_.MIPStarRE.QPBT.inv_sqrt_natCast_mul_self n

























































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

theorem solution :
    _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation (K := K) (ι := ι) .X * _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation .Z =
      Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (ι → K) x)
        (fun y => star (_root_.MIPStarRE.QPBT.eprState (ι → K) y)) := by
  ext x y
  rw [Matrix.mul_apply]
  simp_rw [_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation_Z_apply]
  rw [Finset.sum_eq_single y]
  · by_cases hy : y.1 = y.2
    · rcases y with ⟨a, b⟩
      dsimp only at hy
      subst b
      rw [if_pos ⟨rfl, rfl⟩, mul_one, _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation_X_apply_diagonal]
      change (if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0) =
        (if x.1 = x.2 then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0) *
          star (if a = a then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0)
      by_cases hx : x.1 = x.2
      · rw [if_pos hx, if_pos hx, if_pos rfl]
        exact (_root_.MIPStarRE.QPBT.inv_sqrt_natCast_mul_conj (Fintype.card (ι → K))).symm
      · simp [hx]
    · simp [hy, Matrix.vecMulVec_apply, _root_.MIPStarRE.QPBT.eprState]
  · intro z _ hz
    simp [hz]
  · simp
