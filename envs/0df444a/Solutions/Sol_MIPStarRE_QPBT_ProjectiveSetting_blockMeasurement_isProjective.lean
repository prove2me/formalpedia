-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.blockMeasurement_isProjective
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:17:33.771679+00:00
-- url     : https://prove2.me/submissions/b45892d6-906a-4cc7-be03-17b82f7b5357

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.blockMeasurement_isProjective.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Extraction_BlockMeasurement
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.SymmetrizationObstruction
end MIPStarRE.QPBT.SymmetrizationObstruction

/- Source helpers from QPBT/Games/StrategyClasses.lean. -/
/-! # Strategy classes and symmetric games

This module defines projective, commuting, consistent, PCC, and SPCC strategy
predicates from blueprint `def:projective-strategy-general`,
`def:symmetric-game`, `def:comm-strategy`, `def:consistent-measurement`,
`def:consistent-strategy`, and `def:spcc`, with source definitions in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:68-180`.
-/
@[expose] public section
namespace MIPStarRE.QPBT

universe u

open scoped BigOperators Matrix MatrixOrder ComplexOrder

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum





attribute [instance] _root_.MIPStarRE.QPBT.SymmetricGame.questionFintype _root_.MIPStarRE.QPBT.SymmetricGame.answerFintype
  _root_.MIPStarRE.QPBT.SymmetricGame.questionDecidableEq _root_.MIPStarRE.QPBT.SymmetricGame.answerDecidableEq





attribute [instance] _root_.MIPStarRE.QPBT.SymmetricStrategy.ιFintype _root_.MIPStarRE.QPBT.SymmetricStrategy.ιDecidableEq



















noncomputable section

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
open LIDT.MIPStarRE.LDT.Preliminaries








































/-- Reindexing a projective POVM preserves projectivity. -/
theorem reindexMeasurement_isProjective
    {α I J : Type*} [Fintype α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α J)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.reindexMeasurement e M) := by
  intro a
  change _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.reindexOp e (M.effect a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) *
        (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a) =
      (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (M.effect a)
    rw [← map_mul, (hM a).isIdempotentElem.eq]
  · exact (Matrix.IsHermitian.ext fun i j => by
      simp [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply,
        (hM a).isSelfAdjoint.isHermitian.apply]).isSelfAdjoint




































end

end MIPStarRE.QPBT

/-!
# Measurements on extraction blocks

This module places a complete measurement from either player's three-register
extraction block on the full six-register space. It also records the transport
of original-player consistency through the two adjoined EPR states.

## References

These are finite-dimensional placement lemmas supporting blueprint
`lem:qld-construct-the-paulis` and `lem:qld-unitary`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

theorem solution (side : _root_.MIPStarRE.QPBT.PlayerSide) {α : Type*} [Fintype α]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.ExtractionBlock P (S.LocalSpace side)))
    (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective A) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.blockMeasurement side A) := by
  classical
  let e := _root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  letI : DecidableEq (_root_.MIPStarRE.QPBT.ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · have h := _root_.MIPStarRE.QPBT.reindexMeasurement_isProjective e (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement A)
      (fun a => _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker (hA a)
        (IsStarProjection.one _))
    convert h using 1
    rfl
  · have h := _root_.MIPStarRE.QPBT.reindexMeasurement_isProjective e (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement A)
      (fun a => _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
        (IsStarProjection.one _) (hA a))
    convert h using 1
    rfl
