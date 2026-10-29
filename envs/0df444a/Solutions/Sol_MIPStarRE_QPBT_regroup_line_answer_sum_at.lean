-- Prove2me | solution 1 for MIPStarRE.QPBT.regroup_line_answer_sum_at
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:56.718311+00:00
-- url     : https://prove2.me/submissions/f17c4bdc-feb3-4f6c-87ac-99504b037c50

-- Generated proof for MIPStarRE.QPBT.regroup_line_answer_sum_at.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Regrouping the line answers by their evaluations -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (G : Option (_root_.MIPStarRE.QPBT.PauliScalar P) → Option (_root_.MIPStarRE.QPBT.PauliScalar P) →
      _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace second.side)) :
    (∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side lineX lineZ).postprocess (fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1, _root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2)))).effect o *
            S.place second (G o.1 o.2))) =
      ∑ fX, ∑ fZ, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
          S.place second (G (_root_.MIPStarRE.QPBT.evalOpt lineX x fX) (_root_.MIPStarRE.QPBT.evalOpt lineZ z fZ))) := by
  classical
  have hsum : ∀ (s : Finset (_root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
        _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)))
      (M : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
        _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) →
        _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace first.side))
      (N : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB)),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place first (∑ fs ∈ s, M fs) * N) =
        ∑ fs ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place first (M fs) * N) := by
    intro s M N
    rw [S.place_finsetSum]
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, Finset.sum_mul]
  calc
    (∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side lineX lineZ).postprocess (fun fs =>
                (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1, _root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2)))).effect o *
              S.place second (G o.1 o.2))) =
        ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1, _root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2) = o),
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second (G o.1 o.2)) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
      exact hsum _ _ _
    _ = ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
          ∑ fs ∈ Finset.univ.filter (fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1, _root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2) = o),
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
              (S.place first ((lines.T first.side lineX lineZ).effect fs) *
                S.place second
                  (G (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1) (_root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2))) := by
      refine Finset.sum_congr rfl fun o _ =>
        Finset.sum_congr rfl fun fs hfs => ?_
      rw [← (Finset.mem_filter.mp hfs).2]
    _ = ∑ fs : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d) ×
          _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d),
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
            (S.place first ((lines.T first.side lineX lineZ).effect fs) *
              S.place second
                (G (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1) (_root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2))) :=
      Finset.sum_fiberwise_of_maps_to (fun fs _ => Finset.mem_univ _) _
    _ = ∑ fX, ∑ fZ, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place first ((lines.T first.side lineX lineZ).effect (fX, fZ)) *
            S.place second (G (_root_.MIPStarRE.QPBT.evalOpt lineX x fX) (_root_.MIPStarRE.QPBT.evalOpt lineZ z fZ))) :=
      Fintype.sum_prod_type (f := fun fs => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place first ((lines.T first.side lineX lineZ).effect fs) *
          S.place second (G (_root_.MIPStarRE.QPBT.evalOpt lineX x fs.1) (_root_.MIPStarRE.QPBT.evalOpt lineZ z fs.2))))
