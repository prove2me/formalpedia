-- Prove2me | solution 1 for MIPStarRE.QPBT.stateQForm_placeSide_bob_tensor_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:24:45.440063+00:00
-- url     : https://prove2.me/submissions/67ab01fa-80e8-436b-8f59-595c7880822e

-- Generated proof for MIPStarRE.QPBT.stateQForm_placeSide_bob_tensor_one.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AB_prime_prime_BB_prime

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference measurements and comparison estimates express the convolution
  with the ideal Pauli point projectors.
- These are auxiliary estimates for a supplied witness, not its construction.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder
open scoped Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.ProjectiveSetting







open MIPStarRE.QPBT.ProjectiveSetting

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob))
    (hB : B.IsHermitian) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)))) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) (_root_.MIPStarRE.QPBT.heteroKron 1 B) := by
  have hplace : S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) =
      S.place .BB' B := by
    ext row col
    simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.heteroKron,
      Matrix.kronecker, Matrix.one_apply, mul_ite, ite_mul]
    split_ifs <;> simp_all
  rw [hplace]
  have h := _root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AB_prime_prime_BB_prime S 1 B
    Matrix.isHermitian_one hB
  have hone : S.place .AB'' (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) = 1 := by
    convert S.place_one .AB'' using 1
  rw [hone, Matrix.one_mul] at h
  exact h.symm
