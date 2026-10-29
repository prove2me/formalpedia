-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.place_BB_prime_mul_AB_prime_prime_comm
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.530983+00:00
-- url     : https://prove2.me/submissions/24e24f6b-1241-40b0-b542-e461e1192779

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.place_BB'_mul_AB''_comm.
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
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/FactorTransport.lean. -/
/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/

/-- Left and right placements of local operators commute.  Formalization-only
support for `def:consistency`, blueprint `ch12_qpbt_games.tex:210-223`. -/
theorem heteroKron_left_right_comm {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) * _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B * _root_.MIPStarRE.QPBT.heteroKron A 1 := by
  rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul, one_mul, mul_one]

/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e (M * N) = _root_.MIPStarRE.QPBT.reindexOp e M * _root_.MIPStarRE.QPBT.reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp (fun l : κ => M (e i) l * N l (e j))]





/-! ## Transport of the phase-signed operator distance -/





end WinImplications

end

end MIPStarRE.QPBT

/-!
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
-/

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (A : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .alice))
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .bob)) :
    setting.place .BB' B * setting.place .AB'' A =
      setting.place .AB'' A * setting.place .BB' B := by
  change _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) at A
  change _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) at B
  let e := _root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition P
    setting.toStrategy.ιA setting.toStrategy.ιB
  let I_A : _root_.LIDT.MIPStarRE.Quantum.Op (setting.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) := 1
  let I_R : _root_.LIDT.MIPStarRE.Quantum.Op ((setting.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
      (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)) := 1
  let C := _root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))
  let L := _root_.MIPStarRE.QPBT.heteroKron A I_R
  let R := _root_.MIPStarRE.QPBT.heteroKron I_A C
  have hleft : _root_.MIPStarRE.QPBT.reindexOp e L = setting.place .AB'' A := by
    simpa [e, L, I_R] using
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_left setting A)
  have hright : _root_.MIPStarRE.QPBT.reindexOp e R = setting.place .BB' B := by
    simpa [e, R, I_A, C] using
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_right setting B)
  have hcomm : R * L = L * R := by
    simpa [R, L, I_A, I_R] using
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_right_comm A C).symm
  calc
    setting.place .BB' B * setting.place .AB'' A =
        _root_.MIPStarRE.QPBT.reindexOp e R * _root_.MIPStarRE.QPBT.reindexOp e L :=
      congrArg₂ (fun X Y => X * Y) hright.symm hleft.symm
    _ = _root_.MIPStarRE.QPBT.reindexOp e (R * L) :=
      (_root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul e _ _).symm
    _ = _root_.MIPStarRE.QPBT.reindexOp e (L * R) := congrArg (_root_.MIPStarRE.QPBT.reindexOp e) hcomm
    _ = _root_.MIPStarRE.QPBT.reindexOp e L * _root_.MIPStarRE.QPBT.reindexOp e R :=
      _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul e _ _
    _ = setting.place .AB'' A * setting.place .BB' B :=
      congrArg₂ (fun X Y => X * Y) hleft hright
