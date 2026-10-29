-- Prove2me | solution 1 for MIPStarRE.QPBT.mass_outside_support_le_point_defect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:44.860453+00:00
-- url     : https://prove2.me/submissions/805e60c5-d444-46ad-a413-9075a79dc45e

-- Generated proof for MIPStarRE.QPBT.mass_outside_support_le_point_defect.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ





























































end MIPStarRE.QPBT.DistanceCalculus

/-! # Marginal mass outside the support of a reference measurement

A complete reference measurement supported on an allowed outcome set bounds
the other measurement's mass outside that set by their bipartite consistency
defect. The measurements act on separate tensor factors of the same state.
Neither projectivity nor state normalization is needed; for a unit vector the
quadratic forms are the corresponding Born probabilities.

These are formalization-only auxiliary estimates for the non-encoding mass
calculation in blueprint `eq:qld-nonencoding-mass`. They can be composed with
the codeword-defect comparison after constructing an encoding-supported
reference measurement on the opposite tensor factor. They do not construct
that reference or establish its evaluated consistency, and do not prove the
non-encoding marginal-mass bound or global-pair witness existence.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1498`,
  the consistency calculation in `lem:qld-construct-the-paulis` that the
  blueprint's non-encoding mass estimate supports.
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`,
  the bipartite consistency defect.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {Outcome Left Right : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (meas : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Left) (reference : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Right)
    (psi : EuclideanSpace ℂ (Left × Right)) (allowed : Finset Outcome)
    (hsupport : ∀ outcome, outcome ∉ allowed → reference.effect outcome = 0) :
    (∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) 1)) ≤
      ∑ outcome : Outcome, ∑ other : Outcome, if outcome = other then 0 else
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) (reference.effect other)) := by
  have hnonneg (outcome other : Outcome) :
      0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) (reference.effect other)) :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg psi (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (meas.pos outcome) (reference.pos other))
  calc
    (∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) 1)) =
        ∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
          ∑ other : Outcome, if outcome = other then 0 else
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi
              (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) (reference.effect other)) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      have hzero := hsupport outcome (Finset.mem_filter.mp houtcome).2
      rw [← reference.sum_eq_one, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
      apply Finset.sum_congr rfl
      intro other _
      by_cases heq : outcome = other
      · subst other
        simp [hzero, _root_.MIPStarRE.QPBT.heteroKron, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
      · rw [if_neg heq]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro outcome _ _
      apply Finset.sum_nonneg
      intro other _
      split_ifs
      · exact le_rfl
      · exact hnonneg outcome other
