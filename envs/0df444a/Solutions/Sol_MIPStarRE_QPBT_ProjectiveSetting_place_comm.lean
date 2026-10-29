-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.place_comm
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.413021+00:00
-- url     : https://prove2.me/submissions/f272a0e3-e112-48b9-ab84-bebc2eb90692

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.place_comm.
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
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
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

set_option synthInstance.maxSize 400 in

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    ∀ (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement), p₁.IsOpposite p₂ →
      ∀ (A : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side))
        (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side)),
        S.place p₁ A * S.place p₂ B = S.place p₂ B * S.place p₁ A
  | .AA', .BA'', _, A, B => by
      classical
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AA'_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BA''_eq, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
        ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
      simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, one_mul, mul_one]
  | .BA'', .AA', _, A, B => by
      classical
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AA'_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BA''_eq, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
        ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
      simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, one_mul, mul_one]
  | .BB', .AB'', _, A, B => by
      classical
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_eq, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
        ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
      simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, one_mul, mul_one]
  | .AB'', .BB', _, A, B => by
      classical
      rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.place_AB''_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_BB'_eq, ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
        ← _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul]
      simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, one_mul, mul_one]
  | .AA', .AA', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .AA', .BB', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .AA', .AB'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BA'', .BA'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BA'', .BB', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BA'', .AB'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BB', .AA', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BB', .BA'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .BB', .BB', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .AB'', .AA', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .AB'', .BA'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
  | .AB'', .AB'', h, _, _ => by simp [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at h
