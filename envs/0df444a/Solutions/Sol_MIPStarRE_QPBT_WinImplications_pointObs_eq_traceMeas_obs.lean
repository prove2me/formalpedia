-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.pointObs_eq_traceMeas_obs
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:51.752956+00:00
-- url     : https://prove2.me/submissions/e6503b84-f0ee-48e9-af90-fb21e729eea9

-- Generated proof for MIPStarRE.QPBT.WinImplications.pointObs_eq_traceMeas_obs.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_PointObs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Self-consistency of the strategy point observables

This module converts the trace-coarse-grained point consistency of item 1 of
`lem:qld-win-implications` into the observable relation
`eq:pts-obs-consistency` of `lem:qld-win-implications-obs`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:294-308`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Linearity of the tensor placement -/







/-! ## The point observable as a binary observable -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyPointObs

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W r u =
      ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • (S.pointTraceMeas side W u r).effect b := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r))
    (t := (Finset.univ : Finset (ZMod 2)))
    (fun a _ => Finset.mem_univ _)
    (f := fun a => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * r)) •
      (S.pointMeas side W u).effect a)]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointTraceMeas,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]
