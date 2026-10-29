-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.norm_heteroKron_pauliCorrelation_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.372416+00:00
-- url     : https://prove2.me/submissions/54b47085-b1d6-4c3a-9360-4c05248160ef

-- Generated proof for MIPStarRE.QPBT.Extraction.norm_heteroKron_pauliCorrelation_apply_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Extraction_EPRProjection
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedCommutation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Observables/ExpandedCommutation.lean. -/
/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Algebraic preliminaries -/



/-- The generalized Pauli observables are reflections. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1089`. -/
theorem tauObservable_conjTranspose_mul_self {K ι : Type*} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : _root_.MIPStarRE.QPBT.PauliKind) (v : ι → K) :
    (_root_.MIPStarRE.QPBT.tauObservable W v)ᴴ * _root_.MIPStarRE.QPBT.tauObservable W v = 1 := by
  rw [_root_.MIPStarRE.QPBT.tauObservable_conjTranspose, _root_.MIPStarRE.QPBT.tauObservable_sq]



end

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

theorem solution {R : Type*}
    [Fintype R] [DecidableEq R] (W : _root_.MIPStarRE.QPBT.PauliKind)
    (ψ : EuclideanSpace ℂ (R × ((ι → K) × (ι → K)))) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation W)) ψ‖ ≤ ‖ψ‖ := by
  let U (u : ι → K) :=
    _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (_root_.MIPStarRE.QPBT.tauObservable W u))
  have hnorm (u : ι → K) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (U u) ψ‖ = ‖ψ‖ := by
    apply _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    simp only [U, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
    change _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u)ᴴ (_root_.MIPStarRE.QPBT.tauObservable W u)ᴴ) *
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (_root_.MIPStarRE.QPBT.tauObservable W u)) = 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.tauObservable_conjTranspose_mul_self,
      _root_.MIPStarRE.QPBT.heteroKron_one_one, Matrix.one_mul, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  have haction : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation W)) ψ =
      (Fintype.card (ι → K) : ℂ)⁻¹ • ∑ u : ι → K,
        _root_.MIPStarRE.QPBT.applyOperatorToState (U u) ψ := by
    change _root_.MIPStarRE.QPBT.applyOperatorToState
      ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : _root_.LIDT.MIPStarRE.Quantum.Op R))
        ((Fintype.card (ι → K) : ℂ)⁻¹ •
          ∑ u : ι → K, _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) (_root_.MIPStarRE.QPBT.tauObservable W u))) ψ = _
    simp only [map_smul, map_sum, _root_.MIPStarRE.QPBT.applyOperatorToState, LinearMap.sum_apply,
      LinearMap.smul_apply]
    rfl
  rw [haction, norm_smul]
  calc
    _ ≤ ‖(Fintype.card (ι → K) : ℂ)⁻¹‖ * ∑ u : ι → K,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (U u) ψ‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖ψ‖ := by
      simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀, one_mul]
      positivity
