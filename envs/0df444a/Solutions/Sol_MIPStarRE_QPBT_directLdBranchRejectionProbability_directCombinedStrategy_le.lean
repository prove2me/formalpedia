-- Prove2me | solution 1 for MIPStarRE.QPBT.directLdBranchRejectionProbability_directCombinedStrategy_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.580992+00:00
-- url     : https://prove2.me/submissions/5d987b87-55a6-479a-aab2-52c1aa71535c

-- Generated proof for MIPStarRE.QPBT.directLdBranchRejectionProbability_directCombinedStrategy_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_QuestionLaw
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Value
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionMarginals
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_equiv_prod
import Theorems.Thm_MIPStarRE_QPBT_avgOver_directCombinedMeasuredRejectedMass_coefficientVar
import Theorems.Thm_MIPStarRE_QPBT_directLdBranchRejectionProbability_nonneg
import Theorems.Thm_MIPStarRE_QPBT_directRejectedMass_directCombinedStrategy_le_measured

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section









instance instNonemptyFinM_1 (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩



















/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/BranchComparison.lean. -/
/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Rejected Born mass at a fixed question pair -/





/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D)) fun sample =>
        _root_.MIPStarRE.QPBT.directRejectedMass D S
          (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 sample)
          (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 sample) :=
  rfl



/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/















/-! ## Direct samples as products -/



/-! ## The point-agreement and axis-line branches -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/QuestionLaw.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.directCombinedIndexNonempty
/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section



/-! ## Coordinates of the combined dimension -/













/-! ## Canonical bases -/







/-! ## The measured questions -/







/-! ## The law of the projected sample -/











/-- The distributional half of `lem:ld-combined-question-law`: the coordinate
index of a uniform sample of the combined game and the two point parts of that
sample are jointly uniform on the product of the `m + k` coordinates with two
copies of `F_q^m`.  Conditioned on a point coordinate index, the point parts
are therefore uniform, so by
`directCombined_measuredQuestion_of_pointVar` the questions measured by the
combined strategy are the canonical questions of a uniform sample of the
original game at the same ordered type pair; conditioned on a combining
coordinate index, the point part of the sampled point is uniform, so by
`directCombined_measuredQuestion_of_coefficientVar` both measured questions are
the point question at a uniform point.  This single statement subsumes the two
marginal laws `directCombinedSample_pointParts_uniform` and
`directCombinedSample_index_uniform`, which it refines by recording that the
index and the point parts are independent. -/
theorem directCombinedSample_indexPointParts_uniform (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D.combined)).map
        (fun sample => (sample.index,
          (_root_.MIPStarRE.QPBT.directCombinedPointPart D sample.point,
            _root_.MIPStarRE.QPBT.directCombinedPointPart D sample.direction))) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (Fin D.combined.m ×
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))) :=
  _root_.MIPStarRE.QPBT.uniformDistribution_map_fst_of_equiv (e := directCombinedSpaceIndexEquiv D) _
    fun _ => rfl

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Value.lean. -/
/-!
# The value of the combined strategy

`lem:ld-combined-value` transports the value of a projective strategy along
`def:ld-combined-strategy`.  Both games weight their nine ordered type pairs
uniformly, so it suffices to bound the rejection probability of each branch of
the combined game by a bounded number of branch rejection probabilities of the
original game.  Splitting a branch according to the event of
`lem:ld-combined-question-law`, the branch conditioned on a point coordinate
index is the branch of the original game at the same ordered type pair, and the
branch conditioned on a combining coordinate index is the point-versus-point
branch of the original game; on each of the two events the relabelling of
`def:ld-combined-strategy` carries acceptance to acceptance, which is
`directCombinedWinTransport_all`.  Each branch of the combined game is therefore
rejected with probability at most the sum of two branch rejection probabilities
of the original game, and summing over the nine branches multiplies the
rejection probability by at most ten.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section





/-- Conditioned on a point coordinate index, the measured pair is the canonical
pair of the original game at the same ordered type pair attached to a uniform
sample. -/
theorem avgOver_directCombinedMeasuredRejectedMass_pointVar (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) (j : Fin D.m) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
      (_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types
        (_root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j)) =
      _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types j := by
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro pd
  simp only [_root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass,
    _root_.MIPStarRE.QPBT.directCombinedIndexSplit_combinedPointVar]









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/GameValue.lean. -/
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

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The index-conditioned branch rejection probability -/





/-- The branch rejection probability of an ordered type pair is the uniform
average over the stored coordinate index of the index-conditioned rejection
probabilities.  This is the refinement used to split a branch of the combined
game according to the event of `lem:ld-combined-question-law`, whose two cases
are the point coordinates and the combining coordinates of the combined
dimension. -/
theorem directLdBranchRejectionProbability_eq_avgOver_index
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m))
        (_root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod (e := _root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv D) _

/-! ## The point-versus-point branch -/





/-! ## The rejected mass of the combined strategy -/





end

end MIPStarRE.QPBT

/-!
# The value of the combined strategy

`lem:ld-combined-value` transports the value of a projective strategy along
`def:ld-combined-strategy`.  Both games weight their nine ordered type pairs
uniformly, so it suffices to bound the rejection probability of each branch of
the combined game by a bounded number of branch rejection probabilities of the
original game.  Splitting a branch according to the event of
`lem:ld-combined-question-law`, the branch conditioned on a point coordinate
index is the branch of the original game at the same ordered type pair, and the
branch conditioned on a combining coordinate index is the point-versus-point
branch of the original game; on each of the two events the relabelling of
`def:ld-combined-strategy` carries acceptance to acceptance, which is
`directCombinedWinTransport_all`.  Each branch of the combined game is therefore
rejected with probability at most the sum of two branch rejection probabilities
of the original game, and summing over the nine branches multiplies the
rejection probability by at most ten.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D.combined (_root_.MIPStarRE.QPBT.directCombinedStrategy D S)
        types ≤
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types +
        _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := by
  classical
  have hmpos : 0 < D.m := Nat.lt_of_lt_of_le Nat.zero_lt_one D.hm
  have hkpos : 0 < D.k := Nat.lt_of_lt_of_le Nat.zero_lt_one D.hk
  let _ : Nonempty (Fin D.combined.m) :=
    ⟨⟨0, by change 0 < D.m + D.k; exact Nat.add_pos_left hmpos D.k⟩⟩
  have hstep : _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D.combined
      (_root_.MIPStarRE.QPBT.directCombinedStrategy D S) types ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.combined.m ×
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))))
        (fun x => _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types x.1 x.2) := by
    rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver,
      ← _root_.MIPStarRE.QPBT.directCombinedSample_indexPointParts_uniform D, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun sample =>
      _root_.MIPStarRE.QPBT.directRejectedMass_directCombinedStrategy_le_measured D S types sample
  refine le_trans hstep ?_
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (f := fun i pd =>
      _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types i pd),
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin]
  have hmkNat : D.combined.m = D.m + D.k := rfl
  have hcard : (D.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
  have hmk : ((D.combined.m : ℕ) : ℝ) = (D.m : ℝ) + (D.k : ℝ) := by
    rw [hmkNat]
    push_cast
    ring
  have hsum : ∑ i : Fin D.combined.m,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun pd => _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types i pd) =
      (∑ j : Fin D.m, _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types j) +
        (D.k : ℝ) * _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := by
    show ∑ i : Fin (D.m + D.k),
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
            ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
          (fun pd => _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types i pd) = _
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact _root_.MIPStarRE.QPBT.avgOver_directCombinedMeasuredRejectedMass_pointVar D S types j
    · have hconst : ∀ r : Fin D.k,
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
            (fun pd => _root_.MIPStarRE.QPBT.directCombinedMeasuredRejectedMass D S types
              (Fin.natAdd D.m r) pd) =
            _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) := fun r =>
        _root_.MIPStarRE.QPBT.avgOver_directCombinedMeasuredRejectedMass_coefficientVar D S types r
      simp [hconst, Finset.sum_const, nsmul_eq_mul]
  have hbranch : ∑ j : Fin D.m,
      _root_.MIPStarRE.QPBT.directLdIndexedBranchRejectionProbability D S types j =
      (D.m : ℝ) * _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types := by
    rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver_index,
      _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin]
    field_simp
  rw [hsum, hbranch, hmk]
  have hB : 0 ≤ _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types :=
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg D S types
  have hP : 0 ≤ _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .point) :=
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg D S (.point, .point)
  have hm : (0 : ℝ) < D.m := by exact_mod_cast hmpos
  have hk : (0 : ℝ) < D.k := by exact_mod_cast hkpos
  rw [inv_mul_eq_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hm.le hP, mul_nonneg hk.le hB]
