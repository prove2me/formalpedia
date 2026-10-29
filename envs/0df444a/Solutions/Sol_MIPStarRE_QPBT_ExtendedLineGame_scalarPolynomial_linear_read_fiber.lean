-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial_linear_read_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.545508+00:00
-- url     : https://prove2.me/submissions/23cd1883-8cd6-4150-9f06-f8ab43286c7e

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial_linear_read_fiber.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_RoundedPolynomialEstimates
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ScalarPolynomial
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_scalarPolynomial_eval

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







/-- Exact partial evaluation for either block order. This is the coefficient
specialization used in `eq:qld-g-2`, supporting blueprint `lem:qld-4-7`. -/
theorem blockCoefficientPolynomial_eval (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) (a : Fin 2 →₀ ℕ) (reverse : Bool)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g a reverse)) =
    MvPolynomial.eval (fun i => Sum.elim x z
      (((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
        (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) i))
      ((_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g).coeff a) := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial, eval_sumRingEquiv, MvPolynomial.eval_rename]
  rfl













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
    (hg : ∃ r t : MvPolynomial (Fin (2 * P.m)) (_root_.MIPStarRE.QPBT.PauliScalar P),
      _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial P g = MvPolynomial.C r * MvPolynomial.X 0 +
        MvPolynomial.C t * MvPolynomial.X 1)
    (reverse : Bool) (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (v : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P (_root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse ((z, x), v)) g =
      v 0 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single (if reverse then 1 else 0) 1)
          reverse)) +
      v 1 * MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z)
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial P g (Finsupp.single (if reverse then 0 else 1) 1)
          reverse)) := by
  obtain ⟨r, t, hg⟩ := hg
  let u : Fin (2 * P.m) → _root_.MIPStarRE.QPBT.PauliScalar P := fun i => Sum.elim x z
    (((_root_.MIPStarRE.QPBT.ExtendedLineGame.baseCoordinateEquiv P.m).trans
      (if reverse then Equiv.sumComm _ _ else Equiv.refl _)) i)
  let v' : Fin 2 → _root_.MIPStarRE.QPBT.PauliScalar P := if reverse then ![v 1, v 0] else v
  have heq : _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv P (u, v') =
      _root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv P reverse ((z, x), v) := by
    cases reverse <;> simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.scalarBaseQuestionEquiv, _root_.MIPStarRE.QPBT.ExtendedLineGame.fiberQuestionEquiv, u, v',
      Equiv.piCongrLeft_apply]
  rw [← heq, ← _root_.MIPStarRE.QPBT.ExtendedLineGame.scalarPolynomial_eval, hg]
  simp_rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.blockCoefficientPolynomial_eval, hg]
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  simp only [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  cases reverse <;>
    simp only [Bool.false_eq_true, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h01, Ne.symm h01,
      ↓reduceIte, mul_one, mul_zero, zero_add, add_zero]
  · change MvPolynomial.eval u r * v 0 + MvPolynomial.eval u t * v 1 =
      v 0 * MvPolynomial.eval u r + v 1 * MvPolynomial.eval u t
    ring
  · change MvPolynomial.eval u r * v 1 + MvPolynomial.eval u t * v 0 =
      v 0 * MvPolynomial.eval u t + v 1 * MvPolynomial.eval u r
    ring
