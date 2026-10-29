-- Prove2me | solution 1 for MIPStarRE.QPBT.Extraction.norm_sub_eprProjection_le_of_pauli_dist
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.921655+00:00
-- url     : https://prove2.me/submissions/9f882df3-da62-4488-8b07-8489640f29c2

-- Generated proof for MIPStarRE.QPBT.Extraction.norm_sub_eprProjection_le_of_pauli_dist.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_EPRProjection
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Extraction_norm_heteroKron_pauliCorrelation_apply_le
import Theorems.Thm_MIPStarRE_QPBT_Extraction_norm_sub_pauliCorrelation_sq_le
import Theorems.Thm_MIPStarRE_QPBT_Extraction_pauliCorrelation_mul_eq_epr

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/





/-- Operators act additively on differences of states. -/
theorem applyOperatorToState_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState M (u - v) =
      _root_.MIPStarRE.QPBT.applyOperatorToState M u - _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





























/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# EPR projection from Pauli disagreement

Averaging the paired Pauli operators contracts the disagreement norm. The X
and Z averages multiply to the EPR projection, giving the corrected projection
estimate directly in the squared-distance formulation.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT.Extraction

open LIDT.MIPStarRE.Quantum LIDT.MIPStarRE.LDT MIPStarRE.QPBT.DistanceCalculus



variable {K I R : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem solution
    (psi : EuclideanSpace ℂ (R × ((I → K) × (I → K))))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdist : ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
      _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (I → K))
        (fun u => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.tauObservable W u) 1))
        (fun u => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.tauObservable W u))) psi ≤ delta) :
    ‖psi - _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R)
      (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (I → K) x)
        (fun y => star (_root_.MIPStarRE.QPBT.eprState (I → K) y)))) psi‖ ≤ 2 * Real.sqrt delta := by
  let H (W : _root_.MIPStarRE.QPBT.PauliKind) := _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R) (_root_.MIPStarRE.QPBT.Extraction.pauliCorrelation (K := K) (ι := I) W)
  have hstep (W : _root_.MIPStarRE.QPBT.PauliKind) : ‖psi - _root_.MIPStarRE.QPBT.applyOperatorToState (H W) psi‖ ≤ Real.sqrt delta := by
    have h := (_root_.MIPStarRE.QPBT.Extraction.norm_sub_pauliCorrelation_sq_le W psi).trans (hdist W)
    exact (Real.le_sqrt (norm_nonneg _) hdelta).mpr h
  have hprod : H .X * H .Z = _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op R)
      (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (I → K) x)
        (fun y => star (_root_.MIPStarRE.QPBT.eprState (I → K) y))) := by
    dsimp only [H]
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul, _root_.MIPStarRE.QPBT.Extraction.pauliCorrelation_mul_eq_epr]
  rw [← hprod, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  calc
    _ ≤ ‖psi - _root_.MIPStarRE.QPBT.applyOperatorToState (H .X) psi‖ +
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (H .X) psi -
          _root_.MIPStarRE.QPBT.applyOperatorToState (H .X) (_root_.MIPStarRE.QPBT.applyOperatorToState (H .Z) psi)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt delta + Real.sqrt delta := add_le_add (hstep .X) (by
      rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub]
      exact (_root_.MIPStarRE.QPBT.Extraction.norm_heteroKron_pauliCorrelation_apply_le .X _).trans (hstep .Z))
    _ = 2 * Real.sqrt delta := by ring
