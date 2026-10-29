-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.49127+00:00
-- url     : https://prove2.me/submissions/a68869a2-12a0-4b34-8fd3-a0ec22930c82

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose.
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
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/









/-- Reindexing an operator commutes with the conjugate transpose. -/
theorem reindexOp_conjTranspose {ι κ : Type*} (e : ι ≃ κ) (M : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e Mᴴ = (_root_.MIPStarRE.QPBT.reindexOp e M)ᴴ := by
  ext i j
  rfl



/-! ## The placement is a unital `*`-homomorphism -/























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron A B)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]









/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/





















end WinImplications

end

end MIPStarRE.QPBT

/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/













/-! ## The placement is a unital `*`-homomorphism -/

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    ∀ (p : _root_.MIPStarRE.QPBT.Placement) (A : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p.side)),
      S.place p Aᴴ = (S.place p A)ᴴ
  | .AA', A => by
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AA'_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_AA'_eq, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]
      all_goals rfl
  | .BA'', A => by
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_BA''_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BA''_eq, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        Matrix.conjTranspose_one]
      all_goals rfl
  | .BB', A => by
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_eq, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        Matrix.conjTranspose_one]
      all_goals rfl
  | .AB'', A => by
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_eq, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_conjTranspose,
        _root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]
      all_goals rfl
