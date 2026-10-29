-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.idealExpState_extractionAux0
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:24:57.092393+00:00
-- url     : https://prove2.me/submissions/112f4661-7635-4aff-9da8-247b572fbad2

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.idealExpState_extractionAux0.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EPRState
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Extraction_vecTensor_eprPartialInner

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







open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)

open scoped Classical

theorem solution
    (θ : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    S.idealExpState (S.extractionAux0 θ) =
      _root_.MIPStarRE.QPBT.applyOperatorToState S.extractionEprProjection θ := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.idealExpState _root_.MIPStarRE.QPBT.ProjectiveSetting.extractionAux0
  rw [_root_.MIPStarRE.QPBT.Extraction.vecTensor_eprPartialInner]
  ext x
  let e := (_root_.MIPStarRE.QPBT.extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
  let T := _root_.MIPStarRE.QPBT.heteroKron
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (Matrix.vecMulVec (fun x => _root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) x)
      (fun y => star (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) y)))
  change (T *ᵥ (fun j => θ (e.symm j))) (e x) =
    ((T.submatrix e e) *ᵥ (fun j => θ j)) x
  exact (congrFun (Matrix.submatrix_mulVec_equiv T (fun j => θ j) e e) x).symm
