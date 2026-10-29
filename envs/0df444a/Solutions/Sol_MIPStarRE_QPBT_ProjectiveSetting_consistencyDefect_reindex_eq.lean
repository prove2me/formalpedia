-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_reindex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:16:02.898191+00:00
-- url     : https://prove2.me/submissions/e41c71f5-c4c1-4d6c-ad77-a5282a1cc11d

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_reindex_eq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

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
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Jensen's inequality for the fourth root -/





/-! ## The bipartition with Bob's registers first -/



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





/-! ## Transport along a bipartition -/



variable (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement)

set_option synthInstance.maxSize 400 in

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (e : _root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      S.ExpandedLocalSpace p₁.side ×
        (S.ExpandedLocalSpace p₂.side × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))
    (he₁ : ∀ O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side),
      _root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.heteroKron O
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side ×
          (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) = S.place p₁ O)
    (he₂ : ∀ O : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side),
      _root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side))
        (_root_.MIPStarRE.QPBT.heteroKron O (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
          S.place p₂ O)
    (Q : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (R : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side)) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (Q.effect a) 1)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := _root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P) R).effect a))
        (_root_.MIPStarRE.QPBT.reindexState e S.psiHat) =
      ∑ a : α, ∑ b : α, if a = b then 0 else
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place p₁ (Q.effect a) * S.place p₂ (R.effect b)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg hab, if_neg hab, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm,
      _root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul, he₁]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place p₁ (Q.effect a) *
      _root_.MIPStarRE.QPBT.reindexOp e (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron (R.effect b) 1))) = _
    rw [he₂]
