-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoordinate_diagonal_point_line_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:36:27.73399+00:00
-- url     : https://prove2.me/submissions/5f03527c-c19d-4708-aafe-a4a9563eb35e

-- Generated proof for MIPStarRE.QPBT.directCoordinate_diagonal_point_line_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_BranchComparison
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_DiagonalRecursion
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_equiv_prod
import Theorems.Thm_MIPStarRE_QPBT_directDiagonalIndexOf_eq
import Theorems.Thm_MIPStarRE_QPBT_directPointAnswerReadout_eq_diagonal_zeroCoord_of_win
import Theorems.Thm_MIPStarRE_QPBT_qBipartiteConsDefect_le_directRejectedMass

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Questions.lean. -/
/-!
# Question and answer transport for the directly indexed low-degree game

This module reads low individual degree test questions as canonical direct
questions and rebases direct answers to the LDT line parametrization.

Points and lines are decoded with the coordinate order reversed
(`directPointEquiv`), so that the suffix-zero direction restriction of the
LDT diagonal test becomes the prefix-zero restriction of the direct game.
An LDT diagonal line reveals no coordinate index, whereas a direct diagonal
question carries one.  The transported question uses the *leading index* of
the decoded direction, the least coordinate at which the direction is
nonzero.  Under the direct sampler, this is the index attached to the sampled
direction exactly when the direction is nonzero at the sampled index
(`directDiagonalIndexOf_prefixProjection`), an event of conditional
probability `1 - 1/q`; on the LDT side, the leading index of a decoded
`j`-restricted direction is `Fin.rev j` exactly when its pivot coordinate is
nonzero (`directDiagonalIndexOf_extendRestrictedDirection`).  Diagonal answers
on zero-direction lines are read as the constant polynomial carrying their
value at the base point, following `rem:ld-win-zero-direction`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272`
- `references/ldt-paper/test_definition.tex:49-65`
- `rem:ld-win-zero-direction`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Canonical line rebasing of LDT lines -/











/-! ## The leading index of a direction -/



theorem mem_directionSupport (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (j : Fin D.m) :
    j ∈ _root_.MIPStarRE.QPBT.directionSupport D v ↔ v j ≠ 0 := by
  simp [_root_.MIPStarRE.QPBT.directionSupport]







/-- The leading index of a prefix-projected direction is the projection index
whenever the direction is nonzero there.  This is the generic direct
diagonal sample: the sampled index is recovered from the projected direction
alone. -/
theorem directDiagonalIndexOf_prefixProjection (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (i : Fin D.m) (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (hi : v i ≠ 0) :
    _root_.MIPStarRE.QPBT.directDiagonalIndexOf D (_root_.MIPStarRE.QPBT.directPrefixProjection i v) = i := by
  apply _root_.MIPStarRE.QPBT.directDiagonalIndexOf_eq
  · intro j hj
    simp [_root_.MIPStarRE.QPBT.directPrefixProjection, hj]
  · simpa [_root_.MIPStarRE.QPBT.directPrefixProjection] using hi



/-! ## Decoding LDT points and lines -/















/-- An LDT `j`-restricted diagonal direction decodes to a direct direction
vanishing before index `Fin.rev j`: the suffix restriction of the low
individual degree test is the prefix restriction of the direct game. -/
theorem ldtPointToDirect_extendRestrictedDirection_prefix_zero
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (j : Fin D.m)
    (free : Fin (j.val + 1) → _root_.LIDT.MIPStarRE.LDT.Fq D.toLDTParameters) :
    letI := D.toLDTFieldModel
    ∀ c : Fin D.m, c.val < (Fin.rev j).val →
      _root_.MIPStarRE.QPBT.ldtPointToDirect D (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j free) c = 0 := by
  letI := D.toLDTFieldModel
  intro c hc
  have hj := j.isLt
  have hgt : ¬ (Fin.rev c).val ≤ j.val := by
    rw [Fin.val_rev] at hc ⊢
    omega
  simp only [_root_.MIPStarRE.QPBT.ldtPointToDirect, _root_.MIPStarRE.QPBT.directPointEquiv_symm_apply,
    _root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection, dif_neg hgt]
  exact (_root_.LIDT.MIPStarRE.LDT.FieldModel.equiv (q := D.q)).symm_apply_apply 0



/-! ## Rebasing lines -/





















/-! ## Reading direct answers as LDT answers -/

















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/





















/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/














/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  unfold _root_.MIPStarRE.QPBT.outcomeWeight _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ

























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

/-- Admissible field sizes are positive, so LDT points over a direct
parameter tuple form a nonempty type. -/
instance instNeZeroNatQ (D : _root_.MIPStarRE.QPBT.DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

/-! ## Rejected Born mass at a fixed question pair -/



theorem directRejectedMass_nonneg (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion D) :
    0 ≤ _root_.MIPStarRE.QPBT.directRejectedMass D S x y := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/DiagonalRecursion.lean. -/
/-!
# Diagonal branches of the coordinate strategies of the direct low-degree game

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question of `Transport.Questions` carries the leading index of that direction.
On the generic event that the direction is nonzero at `i`, the leading index
is `i` and the question is the canonical direct question of the direct sample
`(p, i, v)`, where the LDT defect is bounded by the direct rejection.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses to that index with the factor `q⁻¹`, the
probability that the sampled coordinate vanishes; at the last index the zero
direction has the last coordinate as its leading index by convention and no
recursion occurs.  Summing the recursion shows that each LDT diagonal branch
is at most `q / (q - 1) ≤ 2` times the corresponding branch rejection of the
direct game.  The factor is genuine: a strategy that answers the canonical
question of a direction badly and the non-canonical questions of the same
geometric line well has LDT diagonal failure exceeding the direct branch
rejection.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:49-65,130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Direction coordinates and the one-coordinate recursion

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question carries the leading index of that direction.  On the generic event
that the direction is nonzero at `i`, the leading index is `i` and the
question is the canonical direct question of the direct sample `(p, i, v)`.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses with the factor `q⁻¹`, the probability that
the sampled coordinate vanishes.  At the last index the zero direction has the
last coordinate as its leading index by convention, and no recursion occurs. -/

section DirectionCoordinates

variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)

/-- Restricting at an index where the direction vanishes is restricting at the
next index. -/
private theorem directPrefixProjection_succ_of_zero
    (i i' : Fin D.m) (hi : i'.val = i.val + 1)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (hv : v i = 0) :
    _root_.MIPStarRE.QPBT.directPrefixProjection i v = _root_.MIPStarRE.QPBT.directPrefixProjection i' v := by
  funext j
  unfold _root_.MIPStarRE.QPBT.directPrefixProjection
  by_cases hj : j.val < i.val
  · rw [if_pos hj, if_pos (by omega)]
  · by_cases hj' : j.val < i'.val
    · rw [if_neg hj, if_pos hj']
      have hji : j = i := Fin.ext (by omega)
      rw [hji, hv]
    · rw [if_neg hj, if_neg hj']

/-- Restriction beyond a coordinate ignores translation along that
coordinate. -/
private theorem directPrefixProjection_add_single
    (i i' : Fin D.m) (hi : i.val < i'.val)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (c : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directPrefixProjection i' (v + c • Pi.single i (1 : _root_.MIPStarRE.QPBT.DirectScalarQ D)) =
      _root_.MIPStarRE.QPBT.directPrefixProjection i' v := by
  funext j
  unfold _root_.MIPStarRE.QPBT.directPrefixProjection
  by_cases hj : j.val < i'.val
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    have hji : j ≠ i := by
      intro h
      apply hj
      rw [h]
      exact hi
    simp [Pi.single_eq_of_ne hji]

/-- At the last coordinate the restricted direction has that coordinate as
its leading index: either the direction is nonzero there, or the restricted
direction is zero and the leading index of the zero direction is the last
coordinate by convention. -/
private theorem directDiagonalIndexOf_prefixProjection_last
    (i : Fin D.m) (hi : i.val + 1 = D.m) (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directDiagonalIndexOf D (_root_.MIPStarRE.QPBT.directPrefixProjection i v) = i := by
  by_cases hv : v i = 0
  · have hzero : _root_.MIPStarRE.QPBT.directPrefixProjection i v = 0 := by
      funext j
      unfold _root_.MIPStarRE.QPBT.directPrefixProjection
      by_cases hj : j.val < i.val
      · rw [if_pos hj]
        rfl
      · rw [if_neg hj]
        have hji : j = i := Fin.ext (by have := j.isLt; omega)
        rw [hji, hv]
        rfl
    rw [hzero]
    have hsupp : ¬ (_root_.MIPStarRE.QPBT.directionSupport D (0 : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)).Nonempty := by
      rintro ⟨j, hj⟩
      exact (_root_.MIPStarRE.QPBT.mem_directionSupport D 0 j).mp hj rfl
    unfold _root_.MIPStarRE.QPBT.directDiagonalIndexOf
    rw [dif_neg hsupp]
    apply Fin.ext
    rw [Fin.val_rev]
    simp only [_root_.MIPStarRE.QPBT.DirectLdParams.firstIndex]
    omega
  · exact _root_.MIPStarRE.QPBT.directDiagonalIndexOf_prefixProjection D i v hv

/-- Restricting to the vanishing of a coordinate below the restriction index
scales the uniform average by the inverse field size: translation along that
coordinate permutes the directions and preserves the restriction. -/
private theorem avgOver_uniform_coord_zero (i i' : Fin D.m) (hi : i.val < i'.val)
    (G : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => if v i = 0 then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0) =
      (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ)⁻¹ *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun v => G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v)) := by
  classical
  have hshift : ∀ c : _root_.MIPStarRE.QPBT.DirectScalarQ D,
      (∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        if v i = c then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0) =
      ∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        if v i = 0 then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0 := by
    intro c
    refine Fintype.sum_equiv
      (Equiv.addRight ((-c) • Pi.single i (1 : _root_.MIPStarRE.QPBT.DirectScalarQ D))) _ _ ?_
    intro v
    rw [Equiv.coe_addRight, directPrefixProjection_add_single D i i' hi]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      add_neg_eq_zero]
  have hsum : (∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D, G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v)) =
      (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ) *
        ∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
          if v i = 0 then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0 := by
    calc
      (∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D, G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v)) =
          ∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D, ∑ c : _root_.MIPStarRE.QPBT.DirectScalarQ D,
            if v i = c then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_ite_eq]
        simp
      _ = ∑ c : _root_.MIPStarRE.QPBT.DirectScalarQ D, ∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
            if v i = c then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0 :=
        Finset.sum_comm
      _ = ∑ c : _root_.MIPStarRE.QPBT.DirectScalarQ D, ∑ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
            if v i = 0 then G (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0 :=
        Finset.sum_congr rfl fun c _ => hshift c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, hsum,
    mul_left_comm, ← mul_assoc ((Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ)⁻¹)
      (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ), inv_mul_cancel₀ hq, one_mul]



/-- The decoded `j`-restricted LDT direction of the free coordinates is the
restriction of the direction at the reversed index. -/
private theorem ldtPointToDirect_extend_restrictedDirectionEquiv (j : Fin D.m)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    letI := D.toLDTFieldModel
    _root_.MIPStarRE.QPBT.ldtPointToDirect D
        (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j (restrictedDirectionEquiv D j v).1) =
      _root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) v := by
  letI := D.toLDTFieldModel
  funext c
  by_cases hc : c.val < (Fin.rev j).val
  · rw [_root_.MIPStarRE.QPBT.ldtPointToDirect_extendRestrictedDirection_prefix_zero D j _ c hc]
    unfold _root_.MIPStarRE.QPBT.directPrefixProjection
    rw [if_pos hc]
  · have hrevj := Fin.val_rev j
    have hrevc := Fin.val_rev c
    have hcm := c.isLt
    have hle : (Fin.rev c).val ≤ j.val := by omega
    unfold _root_.MIPStarRE.QPBT.directPrefixProjection
    rw [if_neg hc]
    simp only [_root_.MIPStarRE.QPBT.ldtPointToDirect, _root_.MIPStarRE.QPBT.directPointEquiv_symm_apply, _root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection,
      dif_pos hle, restrictedDirectionEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    refine congrArg v (Fin.ext ?_)
    change D.m - 1 - (Fin.rev c).val = c.val
    have hm := D.hm
    omega

/-- Averaging over the LDT `j`-restricted diagonal sample is averaging over
a direct point and a direct direction restricted at the reversed index. -/
private theorem avgOver_restrictedDiagonalSample_eq (j : Fin D.m)
    (H : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ) :
    letI := D.toLDTFieldModel
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample D.toLDTParameters j))
        (fun s => H (_root_.MIPStarRE.QPBT.ldtPointToDirect D s.1)
          (_root_.MIPStarRE.QPBT.ldtPointToDirect D (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j s.2))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun pv => H pv.1 (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) pv.2)) := by
  letI := D.toLDTFieldModel
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun u free => H (_root_.MIPStarRE.QPBT.ldtPointToDirect D u)
      (_root_.MIPStarRE.QPBT.ldtPointToDirect D (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j free))),
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun p v => H p (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) v)),
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.MIPStarRE.QPBT.directPointEquiv D)]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro u
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_fst (restrictedDirectionEquiv D j)
    (fun free => H (_root_.MIPStarRE.QPBT.ldtPointToDirect D u)
      (_root_.MIPStarRE.QPBT.ldtPointToDirect D (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j free)))]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro v
  change H (_root_.MIPStarRE.QPBT.ldtPointToDirect D u)
      (_root_.MIPStarRE.QPBT.ldtPointToDirect D (_root_.LIDT.MIPStarRE.LDT.extendRestrictedDirection j (restrictedDirectionEquiv D j v).1)) =
    H ((_root_.MIPStarRE.QPBT.directPointEquiv D).symm u) (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) v)
  rw [ldtPointToDirect_extend_restrictedDirectionEquiv]

end DirectionCoordinates

/-- Geometric-series bookkeeping for the one-coordinate recursion.  If every
term is at most its rejection term plus `q⁻¹` times the term at the next
index, and the term at the last index is at most its rejection term, then the
sum is at most twice the sum of the rejection terms once `q ≥ 2`. -/
private theorem sum_le_two_mul_sum_of_recursion {m : ℕ} (t r : Fin m → ℝ) (q : ℝ)
    (hq : 2 ≤ q) (ht : ∀ i, 0 ≤ t i)
    (hstep : ∀ i i' : Fin m, i'.val = i.val + 1 → t i ≤ r i + q⁻¹ * t i')
    (hlast : ∀ i : Fin m, i.val + 1 = m → t i ≤ r i) :
    ∑ i, t i ≤ 2 * ∑ i, r i := by
  classical
  have hq0 : (0 : ℝ) < q := by linarith
  have hqinv : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
  have hqinv0 : (0 : ℝ) ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  let succSum : Fin m → ℝ := fun i =>
    ∑ i' : Fin m, if i'.val = i.val + 1 then t i' else 0
  have hbound : ∀ i, t i ≤ r i + q⁻¹ * succSum i := by
    intro i
    by_cases h : i.val + 1 < m
    · have hsucc : succSum i = t ⟨i.val + 1, h⟩ := by
        simp only [succSum]
        rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro hb'
          exact hb (Fin.ext hb')
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      rw [hsucc]
      exact hstep i ⟨i.val + 1, h⟩ rfl
    · have hlast' : i.val + 1 = m := by
        have := i.isLt
        omega
      have hsucc : succSum i = 0 := by
        simp only [succSum]
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg]
        intro h'
        have := i'.isLt
        omega
      rw [hsucc, mul_zero, add_zero]
      exact hlast i hlast'
  have hsuccSum : ∑ i, succSum i ≤ ∑ i, t i := by
    simp only [succSum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card : ℝ) ≤ 1 := by
      have h1 : (Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact Fin.ext (by omega)
      exact_mod_cast h1
    calc ((Finset.univ.filter fun i : Fin m => i'.val = i.val + 1).card : ℝ) * t i'
        ≤ 1 * t i' := mul_le_mul_of_nonneg_right hcard (ht i')
      _ = t i' := one_mul _
  have htotal : ∑ i, t i ≤ ∑ i, r i + q⁻¹ * ∑ i, t i := by
    calc ∑ i, t i ≤ ∑ i, (r i + q⁻¹ * succSum i) := Finset.sum_le_sum fun i _ => hbound i
      _ = ∑ i, r i + q⁻¹ * ∑ i, succSum i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ i, r i + q⁻¹ * ∑ i, t i := by
        linarith [mul_le_mul_of_nonneg_left hsuccSum hqinv0]
  have hT : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht i
  have hhalf : q⁻¹ * ∑ i, t i ≤ (2 : ℝ)⁻¹ * ∑ i, t i :=
    mul_le_mul_of_nonneg_right hqinv hT
  linarith

section DiagonalRecursion

variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)

/-- One step of the recursion at a fixed point.  On the generic event the
leading index is the sampled index and the LDT defect is bounded by the
direct rejection there; on the vanishing event the restriction agrees with the
restriction at the next index. -/
private theorem diagonal_recursion_step
    (dd : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D v) v)
    (i i' : Fin D.m) (hi : i'.val = i.val + 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun v => rj i (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) +
        (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ)⁻¹ *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun v => dd (_root_.MIPStarRE.QPBT.directPrefixProjection i' v)) := by
  classical
  have hsplit : ∀ v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
      dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v) =
        (if v i = 0 then 0 else dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) +
          (if v i = 0 then dd (_root_.MIPStarRE.QPBT.directPrefixProjection i' v) else 0) := by
    intro v
    by_cases hv : v i = 0
    · rw [if_pos hv, if_pos hv, zero_add,
        directPrefixProjection_succ_of_zero D i i' hi v hv]
    · rw [if_neg hv, if_neg hv, add_zero]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hsplit, _root_.LIDT.MIPStarRE.LDT.avgOver_add,
    avgOver_uniform_coord_zero D i i' (by omega) dd]
  refine add_le_add ?_ le_rfl
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun v => ?_
  by_cases hv : v i = 0
  · rw [if_pos hv]
    exact hrj i _
  · rw [if_neg hv]
    calc dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v) ≤
        rj (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D (_root_.MIPStarRE.QPBT.directPrefixProjection i v))
          (_root_.MIPStarRE.QPBT.directPrefixProjection i v) := hdd _
      _ = rj i (_root_.MIPStarRE.QPBT.directPrefixProjection i v) := by
        rw [_root_.MIPStarRE.QPBT.directDiagonalIndexOf_prefixProjection D i v hv]

/-- At the last index the LDT defect is bounded by the direct rejection
without recursion. -/
private theorem diagonal_recursion_last
    (dd : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (hdd : ∀ v, dd v ≤ rj (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D v) v)
    (i : Fin D.m) (hi : i.val + 1 = D.m) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => rj i (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) := by
  refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun v => ?_
  calc dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v) ≤
      rj (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D (_root_.MIPStarRE.QPBT.directPrefixProjection i v))
        (_root_.MIPStarRE.QPBT.directPrefixProjection i v) := hdd _
    _ = rj i (_root_.MIPStarRE.QPBT.directPrefixProjection i v) := by
      rw [directDiagonalIndexOf_prefixProjection_last D i hi v]

/-- Summed over the restriction index, the LDT diagonal quantities at a
fixed point are at most twice the direct rejections. -/
private theorem diagonal_sum_le
    (dd : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (rj : Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ)
    (hdd0 : ∀ v, 0 ≤ dd v) (hrj : ∀ i v, 0 ≤ rj i v)
    (hdd : ∀ v, dd v ≤ rj (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D v) v) :
    ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => dd (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) ≤
      2 * ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => rj i (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) := by
  have hcard : 2 ≤ Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) := Fintype.one_lt_card
  refine sum_le_two_mul_sum_of_recursion _ _ (Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ)
    (by exact_mod_cast hcard) ?_ ?_ ?_
  · intro i
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun v => hdd0 _
  · intro i i' hi
    exact diagonal_recursion_step D dd rj hrj hdd i i' hi
  · intro i hi
    exact diagonal_recursion_last D dd rj hdd i hi

end DiagonalRecursion

/-! ## The diagonal-line branches -/

section DiagonalBranches

variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)









/-- The canonical direct question of the LDT line of a direct sample. -/
private theorem directDiagonalQuestionOf_ldtDiagonalLineOf_eq
    (p v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directDiagonalQuestionOf D (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) =
      (.dline, ⟨_root_.MIPStarRE.QPBT.lineRepMap v p, _root_.MIPStarRE.QPBT.directDiagonalIndexOf D v, v⟩) := by
  simp [_root_.MIPStarRE.QPBT.directDiagonalQuestionOf, _root_.MIPStarRE.QPBT.ldtDiagonalLineOf, _root_.MIPStarRE.QPBT.ldtPointToDirect]

private theorem directPointQuestionOf_directPointEquiv (p : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directPointQuestionOf D (_root_.MIPStarRE.QPBT.directPointEquiv D p) = _root_.MIPStarRE.QPBT.directLdPointQuestionOf D p := by
  simp [_root_.MIPStarRE.QPBT.directPointQuestionOf, _root_.MIPStarRE.QPBT.ldtPointToDirect]



/-- The LDT diagonal defect with the point on the left is at most the
direct rejection at the canonical question carrying the leading index. -/
private theorem diagonalPointLineDefect_le (p v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    diagonalPointLineDefect D S hS r p v ≤
      diagonalPointLineRejection D S p (_root_.MIPStarRE.QPBT.directDiagonalIndexOf D v) v := by
  letI := D.toLDTFieldModel
  have h := _root_.MIPStarRE.QPBT.qBipartiteConsDefect_le_directRejectedMass D S hS
    (_root_.MIPStarRE.QPBT.directPointQuestionOf D (_root_.MIPStarRE.QPBT.directPointEquiv D p))
    (_root_.MIPStarRE.QPBT.directDiagonalQuestionOf D (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))
    (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)
    (fun b => _root_.MIPStarRE.QPBT.directDiagonalAnswerReadout D r
      (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) b _root_.LIDT.MIPStarRE.LDT.zeroCoord)
    (fun a b hab => _root_.MIPStarRE.QPBT.directPointAnswerReadout_eq_diagonal_zeroCoord_of_win D r
      (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩) a b hab)
  unfold diagonalPointLineDefect diagonalPointLineRejection
  change _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.MIPStarRE.QPBT.strategyQuantumState S)
      (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
        (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
          (S.A (_root_.MIPStarRE.QPBT.directPointQuestionOf D (_root_.MIPStarRE.QPBT.directPointEquiv D p))) (hS.1 _))
        (_root_.MIPStarRE.QPBT.directPointAnswerReadout D r)).toSubMeas
      (_root_.LIDT.MIPStarRE.LDT.postprocess
        (_root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess
          (_root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas
            (S.B (_root_.MIPStarRE.QPBT.directDiagonalQuestionOf D (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩)))
            (hS.2 _))
          (_root_.MIPStarRE.QPBT.directDiagonalAnswerReadout D r
            (_root_.MIPStarRE.QPBT.ldtDiagonalLineOf D ⟨p, D.firstIndex, v⟩))).toSubMeas
        (fun g => g _root_.LIDT.MIPStarRE.LDT.zeroCoord)) ≤ _
  simp only [ProjMeas.postprocess_toSubMeas, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_comp] at h ⊢
  refine le_trans h (le_of_eq ?_)
  rw [directDiagonalQuestionOf_ldtDiagonalLineOf_eq, directPointQuestionOf_directPointEquiv]

/-- Formalization-only decomposition of a fixed ordered branch rejection into
the stored index and the remaining point-direction pair of a direct sample.
This supports the direct-to-LDT comparison corresponding to
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`. -/
theorem directLdBranchRejectionProbability_eq_index_avg (types : _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) :
    _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S types =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m)) fun i =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
            ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))) fun pv =>
          _root_.MIPStarRE.QPBT.directRejectedMass D S
            (types.1, _root_.MIPStarRE.QPBT.directLdMap D types.1 (⟨pv.1, i, pv.2⟩ : _root_.MIPStarRE.QPBT.DirectLdSpace D))
            (types.2, _root_.MIPStarRE.QPBT.directLdMap D types.2 (⟨pv.1, i, pv.2⟩ : _root_.MIPStarRE.QPBT.DirectLdSpace D)) := by
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_avgOver,
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod (_root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv D)]
  rfl

/-- The LDT line of the decoded data of an LDT line is that line. -/
private theorem ldtDiagonalLineOf_decode (u w : _root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters) :
    _root_.MIPStarRE.QPBT.ldtDiagonalLineOf D
        ⟨_root_.MIPStarRE.QPBT.ldtPointToDirect D u, D.firstIndex, _root_.MIPStarRE.QPBT.ldtPointToDirect D w⟩ =
      { base := u, direction := w } := by
  simp [_root_.MIPStarRE.QPBT.ldtDiagonalLineOf, _root_.MIPStarRE.QPBT.ldtPointToDirect]



/-- The LDT `j`-restricted diagonal branch with the point on the left, as
an average of the decoded defect over the point-direction pair. -/
private theorem diagonal_point_line_term_eq (j : Fin D.m) :
    letI := D.toLDTFieldModel
    _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample D.toLDTParameters j))
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).diagonalPointAnswerFamilyA j)
        ((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).diagonalLineAnswerFamilyB j) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))) fun pv =>
        diagonalPointLineDefect D S hS r pv.1 (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) pv.2) := by
  letI := D.toLDTFieldModel
  rw [← avgOver_restrictedDiagonalSample_eq D j (diagonalPointLineDefect D S hS r)]
  unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro s
  unfold diagonalPointLineDefect
  rw [ldtDiagonalLineOf_decode, (_root_.MIPStarRE.QPBT.directPointEquiv D).apply_symm_apply]
  rfl

/-- Summing a decoded diagonal quantity over the reversed index is summing it
over the direct index, and the point average may be taken outside. -/
private theorem sum_rev_avgOver_eq
    (F : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → Fin D.m → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ) :
    ∑ j : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun pv => F pv.1 (Fin.rev j) (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) pv.2)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun v => F p i (_root_.MIPStarRE.QPBT.directPrefixProjection i v)) := by
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
  have hrev := Equiv.sum_comp Fin.revPerm (fun i =>
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun p =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun v => F p i (_root_.MIPStarRE.QPBT.directPrefixProjection i v)))
  simp only [Fin.revPerm_apply] at hrev
  rw [← hrev]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun p v => F p (Fin.rev j) (_root_.MIPStarRE.QPBT.directPrefixProjection (Fin.rev j) v))

/-- The direct index average of a diagonal quantity, with the point average
taken outside. -/
private theorem avgOver_index_eq
    (F : Fin D.m →
      ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m)) (fun i =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)))
          (F i)) =
      (D.m : ℝ)⁻¹ * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) fun p =>
        ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun v => F i (p, v)) := by
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin, _root_.LIDT.MIPStarRE.LDT.avgOver_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun p v => F i (p, v))





end DiagonalBranches

end

end MIPStarRE.QPBT

/-!
# Diagonal branches of the coordinate strategies of the direct low-degree game

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question of `Transport.Questions` carries the leading index of that direction.
On the generic event that the direction is nonzero at `i`, the leading index
is `i` and the question is the canonical direct question of the direct sample
`(p, i, v)`, where the LDT defect is bounded by the direct rejection.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses to that index with the factor `q⁻¹`, the
probability that the sampled coordinate vanishes; at the last index the zero
direction has the last coordinate as its leading index by convention and no
recursion occurs.  Summing the recursion shows that each LDT diagonal branch
is at most `q / (q - 1) ≤ 2` times the corresponding branch rejection of the
direct game.  The factor is genuine: a strategy that answers the canonical
question of a direction badly and the non-canonical questions of the same
geometric line well has LDT diagonal failure exceeding the direct branch
rejection.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:49-65,130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Direction coordinates and the one-coordinate recursion

The LDT `j`-restricted diagonal sampler decodes to a direct direction with
vanishing prefix below the reversed index `i = Fin.rev j`, and the transported
question carries the leading index of that direction.  On the generic event
that the direction is nonzero at `i`, the leading index is `i` and the
question is the canonical direct question of the direct sample `(p, i, v)`.
Otherwise the restricted direction is also the restriction at the next index,
so the LDT quantity recurses with the factor `q⁻¹`, the probability that
the sampled coordinate vanishes.  At the last index the zero direction has the
last coordinate as its leading index by convention, and no recursion occurs. -/



variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)





















variable (D : _root_.MIPStarRE.QPBT.DirectLdParams)









/-! ## The diagonal-line branches -/



variable (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

theorem solution :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).diagonalPointLeftLineRightFailureProbability ≤
      2 * _root_.MIPStarRE.QPBT.directLdBranchRejectionProbability D S (.point, .dline) := by
  letI := D.toLDTFieldModel
  unfold _root_.LIDT.MIPStarRE.LDT.ProjStrat.diagonalPointLeftLineRightFailureProbability
  rw [_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability_eq_index_avg, avgOver_index_eq,
    Finset.sum_congr rfl (fun j _ => diagonal_point_line_term_eq D S hS r j),
    sum_rev_avgOver_eq D (fun p _ v => diagonalPointLineDefect D S hS r p v), one_div]
  have hmain :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun p =>
          ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun v => diagonalPointLineDefect D S hS r p (_root_.MIPStarRE.QPBT.directPrefixProjection i v))) ≤
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun p =>
          2 * ∑ i : Fin D.m, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun v => diagonalPointLineRejection D S p i (_root_.MIPStarRE.QPBT.directPrefixProjection i v))) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun p => ?_
    exact diagonal_sum_le D (fun v => diagonalPointLineDefect D S hS r p v)
      (fun i v => diagonalPointLineRejection D S p i v)
      (fun v => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg _ _ _)
      (fun i v => _root_.MIPStarRE.QPBT.directRejectedMass_nonneg D S _ _)
      (fun v => diagonalPointLineDefect_le D S hS r p v)
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul] at hmain
  have hm : (0 : ℝ) ≤ (D.m : ℝ)⁻¹ := by positivity
  calc (D.m : ℝ)⁻¹ * _ ≤ (D.m : ℝ)⁻¹ * (2 * _) := mul_le_mul_of_nonneg_left hmain hm
    _ = _ := by
      simp only [diagonalPointLineRejection, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.directLdPointQuestionOf]
      ring
