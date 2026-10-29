-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:22.924292+00:00
-- url     : https://prove2.me/submissions/7b34f3cd-9e3f-4a6e-98ec-84298f7471fd

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial_eval.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarPolynomial
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directPointExtendedQuestionEquiv_apply

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/ExtendedLineGame/ScalarPolynomial.lean. -/
/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame



























private theorem eval_sumRingEquiv {F A B : Type*} [CommSemiring F]
    (p : MvPolynomial (A ⊕ B) F) (u : B → F) (v : A → F) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u)
      (MvPolynomial.sumRingEquiv F A B p)) = MvPolynomial.eval (Sum.elim v u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]



private theorem scalarBaseQuestionEquiv_direct (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin (2 * P.m) → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P).symm (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv P (u, v)) =
      fun i => (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).symm
        (Sum.elim v u (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m i)) := by
  apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P).injective
  rw [Equiv.apply_symm_apply, _root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv_apply]
  apply Prod.ext
  · apply Prod.ext <;> funext i <;>
      simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv, _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.projX, _root_.MIPStarRE.QPBT.projZ,
        _root_.MIPStarRE.QPBT.embX, _root_.MIPStarRE.QPBT.embZ, _root_.MIPStarRE.QPBT.directPointToPauli, Equiv.piCongrLeft_apply]
  · apply Prod.ext <;>
      simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv, _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv, _root_.MIPStarRE.QPBT.alphaVar, _root_.MIPStarRE.QPBT.betaVar,
        _root_.MIPStarRE.QPBT.directPointToPauli]

















end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Scalar and base coefficients of the rounded polynomial outcomes

The singleton polynomial is transported through the canonical field equivalence
and Mathlib's equivalence between a polynomial in a sum of variables and an
iterated polynomial ring. Its individual-degree certificate controls both levels.
Splitting each base coefficient by either block gives the partial degrees used
in the fiber calculation. Independence of both wrong blocks identifies the
outcome with the existing bounded polynomial-pair combining map.

## References

`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1310-1326`,
the coefficient expansion preceding `eq:qld-g-prime-bound`.
The partial coefficient argument and separated image are at lines 1341--1368,
`eq:qld-g-2` and `eq:qld-g-non-separable`; blueprint `lem:qld-4-7`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



open MIPStarRE.QPBT.ExtendedLineGame

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd)
    (u : Fin (2 * P.m) → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P) :
    MvPolynomial.eval v (MvPolynomial.map (MvPolynomial.eval u) (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g)) =
      _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv P (u, v)) g := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt
  rw [scalarBaseQuestionEquiv_direct]
  have h := (MvPolynomial.eval₂_comp (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom
      (fun i => (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).symm
        (Sum.elim v u (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m i))) (g (0 : Fin 1)).1).symm
  change MvPolynomial.eval₂ (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).toRingHom
      (fun i => _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P ((_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).symm
        (Sum.elim v u (_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseCoordinateEquiv P.m i)))) (g (0 : Fin 1)).1 = _ at h
  simp only [RingEquiv.apply_symm_apply] at h
  exact h
