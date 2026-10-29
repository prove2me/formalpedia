-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.pauliCorrelation_Z_apply
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.496756+00:00
-- url     : https://prove2.me/submissions/290bdcb3-0b66-4001-825e-b32fdd758055

-- Generated proof for MIPStarRE.QPBT.Extraction.pauliCorrelation_Z_apply.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_EPRProjection
import Definitions.Def_QPBT_QPBT_Games_Defs
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_pauliProj_eq_avg_tauObservable

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











































































/-- A phase observable is diagonal, with its phase given by the trace pairing. -/
theorem tauObservable_Z_apply
    {K ι : Type*} [Field K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (a x y : ι → K) :
    _root_.MIPStarRE.QPBT.tauObservable .Z a x y =
      if x = y then _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct a y)) else 0 := by
  change
    (∏ i : ι,
      if x i = y i then _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (a i * y i)) else 0) = _
  rw [Fintype.prod_ite_zero, _root_.MIPStarRE.QPBT.prod_phaseSign_binTrace_dotProduct]
  have hsupport : (∀ i, x i = y i) ↔ x = y :=
    (funext_iff (f := x) (g := y)).symm
  simp only [hsupport]









end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/EPRProjection.lean. -/
/-!
# The EPR projection in Pauli extraction

The product of the averaged, paired X and Z observables is the rank-one
projection onto the EPR vector. This is an algebraic prerequisite for constructing
the auxiliary state in `exists_extractionWitness_ofGlobalPairWitness`.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1725-1742`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT.Extraction

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]



private theorem avg_phaseSign_dotProduct (v : ι → K) :
    (Fintype.card (ι → K) : ℂ)⁻¹ *
        ∑ u : ι → K, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct u v)) =
      if v = 0 then 1 else 0 := by
  have h := congrArg (fun A : _root_.LIDT.MIPStarRE.Quantum.Op (ι → K) => A v v)
    (_root_.MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable .Z (0 : ι → K))
  have hv : _root_.MIPStarRE.QPBT.pauliProj .Z (0 : ι → K) v v = if v = 0 then 1 else 0 := by
    change (∏ i, if v i = 0 then (1 : ℂ) else 0) *
      star (∏ i, if v i = 0 then (1 : ℂ) else 0) = _
    simp only [Fintype.prod_boole, ← funext_iff]
    change (if v = 0 then (1 : ℂ) else 0) * star (if v = 0 then 1 else 0) = _
    split <;> simp
  simp only [dotProduct_zero, map_zero, _root_.MIPStarRE.QPBT.phaseSign, ite_true, one_smul] at h
  rw [hv] at h
  simpa only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    _root_.MIPStarRE.QPBT.tauObservable_Z_apply, ite_true, one_mul] using h.symm











end

end MIPStarRE.QPBT.Extraction

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

theorem solution (x y : (ι → K) × (ι → K)) :
    _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation .Z x y = if x = y ∧ y.1 = y.2 then 1 else 0 := by
  simp only [_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [_root_.MIPStarRE.QPBT.tauObservable_Z_apply]
  by_cases hxy : x = y
  · subst x
    simp only [ite_true, true_and]
    have hphase (u : ι → K) :
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct u y.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct u y.2)) =
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct u (y.1 + y.2))) := by
      rw [← _root_.MIPStarRE.QPBT.phaseSign_add, dotProduct_add, map_add]
    simp_rw [hphase]
    rw [avg_phaseSign_dotProduct]
    letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, CharTwo.add_eq_zero]
  · have h : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
      by_contra h
      push Not at h
      exact hxy (Prod.ext h.1 h.2)
    rcases h with h | h <;> simp [h, hxy]
