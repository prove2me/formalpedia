-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.stateQForm_reindexState
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.27791+00:00
-- url     : https://prove2.me/submissions/0241d3a7-b8c0-44cb-8ed6-494250c4be94

-- Generated proof for MIPStarRE.QPBT.WinImplications.stateQForm_reindexState.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_State
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



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/

theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.reindexState e ψ) T =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.reindexOp e T) := by
  have hstate (k : κ) : (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp k = ψ.ofLp (e.symm k) := rfl
  have hstate_star (k : κ) : star (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp k =
      star (ψ.ofLp (e.symm k)) := congrArg star (hstate k)
  have hop (i j : ι) : _root_.MIPStarRE.QPBT.reindexOp e T i j = T (e i) (e j) := rfl
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Complex.re (∑ k : κ,
      (∑ l : κ, T k l * (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp l) *
        star (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp k)) =
    Complex.re (∑ i : ι, (∑ l : ι, _root_.MIPStarRE.QPBT.reindexOp e T i l * ψ.ofLp l) *
      star (ψ.ofLp i))
  simp_rw [hop, hstate, hstate_star]
  apply congrArg Complex.re
  have hinner (i : ι) : (∑ l : ι, T (e i) (e l) * ψ.ofLp l) =
      ∑ l : κ, T (e i) l * ψ.ofLp (e.symm l) := by
    rw [← e.sum_comp (fun l : κ => T (e i) l * ψ.ofLp (e.symm l))]
    exact Finset.sum_congr rfl (fun l _ => by rw [e.symm_apply_apply])
  calc
    (∑ k : κ, (∑ l : κ, T k l * ψ.ofLp (e.symm l)) *
        star (ψ.ofLp (e.symm k))) =
        ∑ i : ι, (∑ l : κ, T (e i) l * ψ.ofLp (e.symm l)) *
          star (ψ.ofLp (e.symm (e i))) :=
      (e.sum_comp (fun k : κ => (∑ l : κ, T k l * ψ.ofLp (e.symm l)) *
        star (ψ.ofLp (e.symm k)))).symm
    _ = ∑ i : ι, (∑ l : ι, T (e i) (e l) * ψ.ofLp l) * star (ψ.ofLp i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hinner i, e.symm_apply_apply]
