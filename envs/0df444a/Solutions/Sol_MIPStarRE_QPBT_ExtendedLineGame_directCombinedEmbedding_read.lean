-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding_read
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.163993+00:00
-- url     : https://prove2.me/submissions/cd432337-cb40-47e2-a007-5dc58fad8580

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding_read.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PairMeasurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_PairCompletion
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directPointExtendedQuestionEquiv_apply

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/Defs.lean. -/
/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section





















/-- Evaluation of `combinePoly` is the displayed combining formula. -/
theorem combinePoly_eval {K : Type*} [CommSemiring K] {m : ℕ}
    (f g : MvPolynomial (Fin m) K) (u : Fin (2 * m + 2) → K) :
    MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinePoly f g) =
      u (_root_.MIPStarRE.QPBT.alphaVar m) * MvPolynomial.eval (_root_.MIPStarRE.QPBT.projX u) f +
        u (_root_.MIPStarRE.QPBT.betaVar m) * MvPolynomial.eval (_root_.MIPStarRE.QPBT.projZ u) g := by
  change MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinePoly f g) =
    u (_root_.MIPStarRE.QPBT.alphaVar m) * MvPolynomial.eval (u ∘ _root_.MIPStarRE.QPBT.embX m) f +
      u (_root_.MIPStarRE.QPBT.betaVar m) * MvPolynomial.eval (u ∘ _root_.MIPStarRE.QPBT.embZ m) g
  simp [_root_.MIPStarRE.QPBT.combinePoly, MvPolynomial.eval_rename]







































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/PairCompletion.lean. -/
/-!
# Restricting and completing global polynomial-pair measurements

The combining map embeds pairs of bounded individual-degree polynomials into
extended polynomials. Restricting a measurement along this embedding produces a
submeasurement whose missing operator is the sum of the noncombined effects.
Relabeling those effects by one specified pair completes the measurement and
preserves projectivity.

These algebraic constructions do not establish the concentration estimate
`eq:qld-g-non-separable` or the point consistency required by
`exists_globalPairWitness`; those are separate quantitative obligations.

## References

- Blueprint `lem:qld-4-7`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
  `eq:qld-sgg-completeness` and the final completion paragraph.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section









/-- Evaluation of a combined outcome is the affine combination of its two
components.  This is the pointwise algebraic identity used when transferring
the global-pair measurement to the expanded point measurements in
`lem:qld-4-7`, paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1364--1380`.
It is a formalization-only consequence of `def:combine-map`; it does not assert
any consistency or quantitative error estimate.
-/
theorem combinedPolyEmbedding_eval (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.PauliScalar P) (pair : _root_.MIPStarRE.QPBT.PolyPair P) :
    MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair).1 =
      u (_root_.MIPStarRE.QPBT.alphaVar P.m) * _root_.MIPStarRE.QPBT.evalAt .X (_root_.MIPStarRE.QPBT.projX u) pair +
        u (_root_.MIPStarRE.QPBT.betaVar P.m) * _root_.MIPStarRE.QPBT.evalAt .Z (_root_.MIPStarRE.QPBT.projZ u) pair := by
  change MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinePoly pair.1.1 pair.2.1) = _
  rw [_root_.MIPStarRE.QPBT.combinePoly_eval]
  rfl



















open LIDT.MIPStarRE.Quantum DistanceCalculus





end

end MIPStarRE.QPBT

/-!
# Transport of the polynomial-pair completion

The actual singleton outcomes are transported by the canonical field
equivalence before applying the algebraic completion.
Every original outcome is retained, including those outside the combining image.

## References

Paper `eq:qld-sgg-completeness` and the completion paragraph of `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (x : _root_.MIPStarRE.QPBT.ExtendedPointQuestion P) (pair : _root_.MIPStarRE.QPBT.PolyPair P) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) =
      x.2.1 * _root_.MIPStarRE.QPBT.evalAt .X x.1.1 pair + x.2.2 * _root_.MIPStarRE.QPBT.evalAt .Z x.1.2 pair := by
  let u := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P).symm x
  have hx := _root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply P u
  have heval : _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x (_root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair) =
      MvPolynomial.eval (_root_.MIPStarRE.QPBT.directPointToPauli P u) (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair).1 := by
    let p : _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) P.d :=
      _root_.MIPStarRE.QPBT.ExtendedLineGame.directCombinedEmbedding P pair (0 : Fin 1)
    have hp := congrArg Subtype.val ((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPolynomialEquiv P).apply_symm_apply
      (_root_.MIPStarRE.QPBT.combinedPolyEmbedding P pair))
    change MvPolynomial.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom p.1 = _ at hp
    rw [← hp]
    change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (MvPolynomial.eval u p.1) = _
    rw [MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom u p.1).symm
  rw [heval, _root_.MIPStarRE.QPBT.combinedPolyEmbedding_eval]
  have hx' : x = ((_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u), _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u)),
      (_root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.alphaVar P.m), _root_.MIPStarRE.QPBT.directPointToPauli P u (_root_.MIPStarRE.QPBT.betaVar P.m))) :=
    ((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P).apply_symm_apply x).symm.trans hx
  rw [hx']
