-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.exists_unit_aux_near_eprProjection
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:32:47.627233+00:00
-- url     : https://prove2.me/submissions/3dd39a20-c0b2-41e1-9e46-845ef144289c

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.exists_unit_aux_near_eprProjection.
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
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_exists_unit_residual
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_idealExpState_extractionAux0

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Extraction
end MIPStarRE.QPBT.Extraction
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Extraction/EPRState.lean. -/
/-!
# The auxiliary vector from the EPR projection

Taking the partial inner product with the EPR vector constructs the
unnormalized auxiliary vector. Tensoring it with EPR gives exactly the
orthogonal projection of the original vector onto the EPR subspace.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1769-1783`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

noncomputable section





namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)

open scoped Classical

/-- In EPR-first local coordinates, the ideal extraction state is the target
of the existing auxiliary-state normalization theorem. -/
theorem reindexState_idealExpState
    (aux : EuclideanSpace ℂ
      (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.extractionEprFirstEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (S.idealExpState aux) =
      _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) aux) := by
  ext index
  change aux ((index.1.2.1, index.1.2.2), (index.2.2.1, index.2.2.2)) *
      _root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) (index.1.1, index.2.1) =
    _root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P) (index.1.1, index.2.1) * aux (index.1.2, index.2.2)
  exact mul_comm _ _





/-- The reference auxiliary vector has norm one. -/
theorem extractionAuxReference_norm : ‖S.extractionAuxReference‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.extractionAuxReference, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq, _root_.MIPStarRE.QPBT.eprState_norm,
    S.toStrategy.ψ_norm, one_mul]









end ProjectiveSetting

end

end MIPStarRE.QPBT

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
    (θ : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB)) (hθ : ‖θ‖ = 1) :
    ∃ aux : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
      ‖aux‖ = 1 ∧ ‖θ - S.idealExpState aux‖ ≤
        2 * ‖θ - _root_.MIPStarRE.QPBT.applyOperatorToState S.extractionEprProjection θ‖ := by
  let e := _root_.MIPStarRE.QPBT.extractionEprFirstEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have hdist (aux : EuclideanSpace ℂ
      (_root_.MIPStarRE.QPBT.ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
      ‖_root_.MIPStarRE.QPBT.reindexState e θ -
        _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) aux)‖ =
          ‖θ - S.idealExpState aux‖ := by
    rw [← S.reindexState_idealExpState]
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (θ - S.idealExpState aux)
  obtain ⟨aux, haux, hclose⟩ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.exists_unit_residual
    (_root_.MIPStarRE.QPBT.reindexState e θ) (by rwa [_root_.MIPStarRE.QPBT.reindexState_norm_eq])
    S.extractionAuxReference S.extractionAuxReference_norm
    ‖θ - _root_.MIPStarRE.QPBT.applyOperatorToState S.extractionEprProjection θ‖ (S.extractionAux0 θ)
    (((hdist (S.extractionAux0 θ)).trans
      (congrArg (fun v => ‖θ - v‖) (S.idealExpState_extractionAux0 θ))).le)
  exact ⟨aux, haux, (hdist aux).symm.trans_le hclose⟩
