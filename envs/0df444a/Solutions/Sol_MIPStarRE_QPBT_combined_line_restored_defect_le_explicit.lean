-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_line_restored_defect_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:37:56.732258+00:00
-- url     : https://prove2.me/submissions/2cd159be-13c6-4d1f-8740-c57f0a7424ee

-- Generated proof for MIPStarRE.QPBT.combined_line_restored_defect_le_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Lines_CombinedMeasurement
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingDistribution
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingMass
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_combined_line_conditioned_defect_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_nondegenerateLinePastingDist_add_mass
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_outcome_equiv

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/Lines/Conditioning.lean. -/
/-!
# Conditioning the line-pasting distribution

The proof conditions only on nonzero X directions. Conditional collision
bounds apply there, and the discarded probability is restored explicitly.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section









/-- The actual X-outer line sandwich and the supplied completed points satisfy
the mass-restoration inequality on every directed opposite placement. This is
not the final consistency estimate: its right side still contains the
conditioned defect to be bounded by one-sided pasting. Source:
`lem:qld-xz-lines`, paper `14_analysis_of_the_pauli_basis_test.tex:942-963`;
remaining construction recorded in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem ProjectiveSetting.combinedLineMeasurement_consistency_le_conditioned
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
      (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample answer => S.place p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => S.place p2
        (((S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
          (fun polys => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 polys.1,
            _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) S.psiHat ≤
    _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass P.toLdParams *
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist P.toLdParams)
        (fun question answer => S.place p1
          (((points.Q p1.side question.2.2 question.1.2.2).postprocess
            (fun pair => (some pair.1, some pair.2))).effect answer))
        (fun question answer => S.place p2
          (((S.combinedLineMeasurement p2.side question.2.1 question.1.2.1).postprocess
            (fun polys => (_root_.MIPStarRE.QPBT.evalOpt question.2.1 question.2.2 polys.1,
              _root_.MIPStarRE.QPBT.evalOpt question.1.2.1 question.1.2.2 polys.2))).effect answer)) S.psiHat +
      1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) := by
  exact _root_.MIPStarRE.QPBT.consistencyDefect_le_nondegenerateLinePastingDist_add_mass S p1 p2 hopp
    (fun sample => (points.Q p1.side sample.1.2 sample.2.2).postprocess
      (fun pair => (some pair.1, some pair.2)))
    (fun sample => (S.combinedLineMeasurement p2.side sample.1.1 sample.2.1).postprocess
      (fun polys => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 polys.1,
        _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 polys.2)))

/-! ## Unequal-dimensional bipartite transport -/

open DistanceCalculus in

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/Construction.lean. -/
/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section











/-- Reversing a paired postprocessing reverses the effect's answer index.
This formalization identity is valid without an injectivity assumption on the
evaluation functions, including completed evaluation at a degenerate line. -/
theorem postprocess_pair_swap_effect {answer first second carrier : Type*}
    [Fintype answer] [DecidableEq answer] [Fintype first] [DecidableEq first]
    [Fintype second] [DecidableEq second] [Fintype carrier] [DecidableEq carrier]
    (measurement : _root_.LIDT.MIPStarRE.Quantum.Measurement answer carrier) (evaluate : answer → first × second)
    (output : second × first) :
    (measurement.postprocess (fun answer => (evaluate answer).swap)).effect output =
      (measurement.postprocess evaluate).effect output.swap := by
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  simp [Prod.ext_iff, and_comm]


















end

end MIPStarRE.QPBT

/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Restoring the discarded directions expands the pasted family and its mass estimate.

theorem solution
    (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error pointError : ℝ)
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams)
            (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams))
            (fun sample output => setting.place first
              (((points.Q first.side sample.1.2 sample.2.2).postprocess
                (fun pair => (some pair.1, some pair.2))).effect output))
            (fun sample output => setting.place second
              (((setting.combinedLineMeasurement second.side sample.1.1 sample.2.1).postprocess
                (fun polys => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 polys.1,
                  _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 polys.2))).effect output)) setting.psiHat ≤
            _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams *
              _root_.MIPStarRE.QPBT.heterogeneousPastingError ((params.m * params.d : ℕ) /
                (Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams) : ℝ))
                ((8 * pointError + 2080 * (error + _root_.MIPStarRE.QPBT.deltaLine error)) /
                  _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams) +
              1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams)) := by
  classical
  have hbound := _root_.MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit
    params error pointError setting points first second hopposite
  have hswapPoints (side : _root_.MIPStarRE.QPBT.PlayerSide) (pointX pointZ : Fin params.m → _root_.MIPStarRE.QPBT.PauliScalar params)
      (output : Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.2, some pair.1))).effect output =
      ((points.Q side pointX pointZ).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output.swap :=
    _root_.MIPStarRE.QPBT.postprocess_pair_swap_effect (points.Q side pointX pointZ)
      (fun pair : _root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params => (some pair.1, some pair.2)) output
  have hswapLines (side : _root_.MIPStarRE.QPBT.PlayerSide) (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc params.toLdParams)
      (pointX pointZ : Fin params.m → _root_.MIPStarRE.QPBT.PauliScalar params)
      (output : Option (_root_.MIPStarRE.QPBT.PauliScalar params) × Option (_root_.MIPStarRE.QPBT.PauliScalar params)) :
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (_root_.MIPStarRE.QPBT.evalOpt lineZ pointZ polys.2, _root_.MIPStarRE.QPBT.evalOpt lineX pointX polys.1))).effect
          output =
      ((setting.combinedLineMeasurement side lineX lineZ).postprocess
        (fun polys => (_root_.MIPStarRE.QPBT.evalOpt lineX pointX polys.1, _root_.MIPStarRE.QPBT.evalOpt lineZ pointZ polys.2))).effect
          output.swap :=
    _root_.MIPStarRE.QPBT.postprocess_pair_swap_effect (setting.combinedLineMeasurement side lineX lineZ)
      (fun polys => (_root_.MIPStarRE.QPBT.evalOpt lineX pointX polys.1, _root_.MIPStarRE.QPBT.evalOpt lineZ pointZ polys.2)) output
  simp_rw [hswapPoints, hswapLines] at hbound
  have hswap := _root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv
    (_root_.MIPStarRE.QPBT.nondegenerateLinePastingDist params.toLdParams)
    (Equiv.prodComm (Option (_root_.MIPStarRE.QPBT.PauliScalar params)) (Option (_root_.MIPStarRE.QPBT.PauliScalar params)))
    (fun query output => setting.place first
      (((points.Q first.side query.2.2 query.1.2.2).postprocess
        (fun pair => (some pair.1, some pair.2))).effect output))
    (fun query output => setting.place second
      (((setting.combinedLineMeasurement second.side query.1.1.1 query.1.1.2).postprocess
        (fun polys => (_root_.MIPStarRE.QPBT.evalOpt query.1.1.1 query.2.2 polys.1,
          _root_.MIPStarRE.QPBT.evalOpt query.1.1.2 query.1.2.2 polys.2))).effect output)) setting.psiHat
  have hnatural := hswap.symm.trans_le hbound
  refine (setting.combinedLineMeasurement_consistency_le_conditioned
    points first second hopposite).trans ?_
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.MIPStarRE.QPBT.nondegenerateLinePastingDist at hnatural ⊢
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map] at hnatural ⊢
  have hmass : 0 ≤ _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams :=
    (_root_.MIPStarRE.QPBT.prod_linePointDist_nondegenerate_mass_pos params.toLdParams).le
  exact add_le_add (mul_le_mul_of_nonneg_left hnatural hmass) le_rfl
