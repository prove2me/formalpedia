-- Prove2me | solution 1 for MIPStarRE.QPBT.outcomeWeight_directCombinedStrategy
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:23.994763+00:00
-- url     : https://prove2.me/submissions/514c5bea-e1f5-49ce-81a8-d41fa82bfa68

-- Generated proof for MIPStarRE.QPBT.outcomeWeight_directCombinedStrategy.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib

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































































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Index-conditioned rejection probabilities of the directly indexed game

`lem:ld-combined-value` transports the value of a strategy along
`def:ld-combined-strategy` by splitting each branch of the combined game
according to the event of `lem:ld-combined-question-law`, that is according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  This module provides the corresponding refinement
of the branch rejection probability: the uniform average over the common sample
is the uniform average over the stored coordinate index of the average over the
sampled point and the sampled direction alone.

The point-versus-point branch is recorded separately, because it is the branch
that the combining coordinates of the combined game reduce to: both of its
questions are the point question at the sampled point, so its rejected mass
depends on neither the stored coordinate index nor the sampled direction.

All declarations below are formalization-only support derived from the game
value; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:517-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## The index-conditioned branch rejection probability -/







/-! ## The point-versus-point branch -/





/-! ## The rejected mass of the combined strategy -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D.combined)
    (a' b' : _root_.MIPStarRE.QPBT.DirectLdAnswer D.combined) :
    _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.directCombinedStrategy D S) x y a' b' =
      ∑ a ∈ Finset.univ.filter (fun a => _root_.MIPStarRE.QPBT.directCombinedAnswerMap D x a = a'),
        ∑ b ∈ Finset.univ.filter (fun b => _root_.MIPStarRE.QPBT.directCombinedAnswerMap D y b = b'),
          _root_.MIPStarRE.QPBT.outcomeWeight S (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D x)
            (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D y) a b := by
  classical
  show _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
      (_root_.MIPStarRE.QPBT.heteroKron
        (((S.A (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D x)).postprocess
            (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D x)).effect a')
        (((S.B (_root_.MIPStarRE.QPBT.directCombinedMeasuredQuestion D y)).postprocess
            (_root_.MIPStarRE.QPBT.directCombinedAnswerMap D y)).effect b')) = _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right,
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  exact Finset.sum_congr rfl fun b _ => rfl
