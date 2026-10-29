-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombinedWinTransport_aline_point
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:11:09.075795+00:00
-- url     : https://prove2.me/submissions/783c536c-48fc-4bdc-8a8e-4fe8f411a300

-- Generated proof for MIPStarRE.QPBT.directCombinedWinTransport_aline_point.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Answers
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_QuestionLaw
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_WinPredicate
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_directCombined_measuredQuestion_of_coefficientVar
import Theorems.Thm_MIPStarRE_QPBT_directCombined_measuredQuestion_of_pointVar

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/Coefficients.lean. -/
/-!
# Coefficient polynomials and finite-field collision bounds

This module supplies the coefficient evaluation and polynomial representation
shared by the low-degree games and the combining argument. Distinct bounded
coefficient vectors agree at no more parameters than their degree bound.

## References

- Blueprint `def:ld-win-predicate` and `lem:coefficient-polynomial-agreement`.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT







/-- Evaluating the polynomial represented by a coefficient list agrees with
`evalCoefficient`. -/
theorem linePolynomialOfCoefficients_eval {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) (t : K) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).eval t = _root_.MIPStarRE.QPBT.evalCoefficient f t := by
  change Polynomial.eval t
      (∑ i ∈ Finset.univ, Polynomial.C (f i) * Polynomial.X ^ i.val) =
    ∑ i ∈ Finset.univ, f i * t ^ i.val
  rw [Polynomial.eval_finsetSum]
  simp

/-- The coefficient sum is the polynomial with coefficient `f i` in degree
`i.val` for `i : Fin (c + 1)` and zero coefficients in degrees greater than `c`. -/
theorem linePolynomialOfCoefficients_eq_ofFn {K : Type*} [Semiring K]
    [DecidableEq K] {c : ℕ} (f : Fin (c + 1) → K) :
    _root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f = Polynomial.ofFn (c + 1) f := by
  simp only [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]



/-- The polynomial of a bounded coefficient vector has degree at most `n`. -/
theorem linePolynomialOfCoefficients_natDegree_le {K : Type*} [Semiring K] {n : ℕ}
    (f : Fin (n + 1) → K) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).natDegree ≤ n := by
  classical
  rw [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eq_ofFn]
  exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos n) f)



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

private theorem directCombinedPointPart_sub_smul (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (z V : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (c : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directCombinedPointPart D (z - c • V) =
      _root_.MIPStarRE.QPBT.directCombinedPointPart D z - c • _root_.MIPStarRE.QPBT.directCombinedPointPart D V :=
  rfl



/-- The canonical base of a line of the combined space projects to a point of
the image line, so rebasing its projection along the image direction returns
the canonical base of the image line.  The canonical base of a line of the
combined space need not itself project to the canonical base of its image; this
is why the answer relabellings of `def:ld-combined-strategy` carry the affine
shift `directCombinedRebaseParameter`. -/
theorem lineRepMap_directCombinedPointPart_lineRepMap (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (V z : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D V)
        (_root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.lineRepMap V z)) =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D V) (_root_.MIPStarRE.QPBT.directCombinedPointPart D z) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span V z)
  have hz : _root_.MIPStarRE.QPBT.lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz, directCombinedPointPart_sub_smul, sub_eq_add_neg, ← neg_smul]
  exact _root_.MIPStarRE.QPBT.lineRepMap_add_smul _ _ (-c)

/-! ## The measured questions -/







/-! ## The law of the projected sample -/













end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Answers.lean. -/
/-!
# Answer polynomials of the combined strategy

The combined strategy of `def:ld-combined-strategy` answers every question of
the directly indexed low-degree game at the combined parameters by measuring a
single question of the original game and relabelling its outcome.  Four of its
five cases produce a line answer, that is a bounded coefficient vector, from a
line answer or from a point answer of the original game.  This module collects
the univariate polynomials underlying those relabellings, with their degree
bounds and their evaluation identities.

Line answers of both games are bounded coefficient vectors evaluated by
`evalCoefficient`.  The polynomials below are therefore built from
`linePolynomialOfCoefficients` and converted back to coefficient vectors by
`coefficientsOfPolynomial`; the degree bounds are what makes that round trip
faithful.

The parameter `s` in the two line cases is the affine shift relating the two
canonical parametrizations of the line.

## Main definitions

* `coefficientsOfPolynomial` — the bounded coefficient vector of a polynomial.
* `shiftedLinePolynomial` — the affine reparametrization of a line answer.
* `combinedAxisPolynomial` — case 2 of `def:ld-combined-strategy`.
* `combinedDiagonalPolynomial` — case 4 of `def:ld-combined-strategy`.
* `fiberLinePolynomial` — cases 3 and 5 of `def:ld-combined-strategy`, the two
  cases whose line lies in a fiber of the projection to the point coordinates.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:420-472`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Coefficient vectors and univariate polynomials -/



/-- A polynomial of degree at most `n` is evaluated by its bounded coefficient
vector of length `n + 1`. -/
theorem evalCoefficient_coefficientsOfPolynomial {K : Type*} [Semiring K] {n : ℕ}
    {p : Polynomial K} (hp : p.natDegree ≤ n) (t : K) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.coefficientsOfPolynomial n p) t = p.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) t,
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (n + 1)]
  rfl



theorem shiftedLinePolynomial_eval {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s t : K) :
    (_root_.MIPStarRE.QPBT.shiftedLinePolynomial f s).eval t = _root_.MIPStarRE.QPBT.evalCoefficient f (t + s) := by
  rw [_root_.MIPStarRE.QPBT.shiftedLinePolynomial, Polynomial.eval_comp]
  simpa using _root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eval f (t + s)

/-- Reparametrizing does not raise the degree of a line answer. -/
theorem shiftedLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {n : ℕ}
    (f : Fin (n + 1) → K) (s : K) :
    (_root_.MIPStarRE.QPBT.shiftedLinePolynomial f s).natDegree ≤ n := by
  refine le_trans Polynomial.natDegree_comp_le ?_
  have hshift : (Polynomial.X + Polynomial.C s : Polynomial K).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp [Polynomial.natDegree_X_le]
  calc (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).natDegree *
        (Polynomial.X + Polynomial.C s : Polynomial K).natDegree
      ≤ n * 1 := Nat.mul_le_mul (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_natDegree_le f) hshift
    _ = n := mul_one n

/-! ## The answer polynomials of the combined strategy -/



theorem combinedAxisPolynomial_natDegree_le {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) :
    (_root_.MIPStarRE.QPBT.combinedAxisPolynomial α s f).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (_root_.MIPStarRE.QPBT.shiftedLinePolynomial_natDegree_le (f r) s)

theorem combinedAxisPolynomial_eval {K : Type*} [CommSemiring K] {k n : ℕ}
    (α : Fin k → K) (s : K) (f : Fin k → Fin (n + 1) → K) (t : K) :
    (_root_.MIPStarRE.QPBT.combinedAxisPolynomial α s f).eval t =
      ∑ r : Fin k, α r * _root_.MIPStarRE.QPBT.evalCoefficient (f r) (t + s) := by
  rw [_root_.MIPStarRE.QPBT.combinedAxisPolynomial, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, _root_.MIPStarRE.QPBT.shiftedLinePolynomial_eval]









theorem fiberLinePolynomial_natDegree_le {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) : (_root_.MIPStarRE.QPBT.fiberLinePolynomial α w b).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (le_of_eq (Polynomial.natDegree_C _)) (Nat.zero_le 1)
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le

theorem fiberLinePolynomial_eval {K : Type*} [CommSemiring K] {k : ℕ}
    (α w b : Fin k → K) (t : K) :
    (_root_.MIPStarRE.QPBT.fiberLinePolynomial α w b).eval t =
      ∑ r : Fin k, (α r + t * w r) * b r := by
  rw [_root_.MIPStarRE.QPBT.fiberLinePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/WinPredicate.lean. -/
/-!
# Branch-wise acceptance transport for the combined strategy

By `directRejectedMass_directCombinedStrategy_le`, the branch-wise estimates of
`lem:ld-combined-value` reduce to the following statement: the relabelling of
`def:ld-combined-strategy` sends an answer pair accepted by the win predicate
of the original game at the measured questions to an answer pair accepted by
the win predicate of the combined game.  This module proves that statement for
each of the nine ordered type pairs of the combined game.

Three of the nine branches are deterministic.  The two questions of a branch
whose type pair is diagonal are equal, so the acceptance clause of the original
game forces the two measured outcomes to be equal, and the relabelling, being a
function, sends them to equal combined outcomes.  The two branches pairing an
axis-parallel line with a diagonal line impose no condition in either game.

The six remaining branches pair a line with a point, and split according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  On a point coordinate the acceptance clause of the
combined game is obtained from the acceptance clause of the original game by
the affine change of parameter `directCombinedRebaseParameter`: the parameter
presenting the sampled point on the sampled line of the combined space presents
the point part of the sampled point on the image line, after the shift.  On a
combining coordinate the sampled line lies in a fiber of the projection to the
point coordinates, the combining part of the sampled point is the affine
function `α₀ + t w` of the parameter, and the acceptance clause of the combined
game is the identity `∑ r (α₀ + t w)_r b_r = ∑ r α_r b_r`.

All declarations below are formalization-only support for
`lem:ld-combined-value`; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two parts of a point along a line -/

theorem directCombinedPointPart_add_smul (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p V : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directCombinedPointPart D (p + t • V) =
      _root_.MIPStarRE.QPBT.directCombinedPointPart D p + t • _root_.MIPStarRE.QPBT.directCombinedPointPart D V := rfl

theorem directCombinedCoefficientPart_add_smul (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p V : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (t : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D (p + t • V) =
      _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D p + t • _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D V := rfl



/-! ## Degree bounds at the combined parameters -/





/-! ## Evaluation of the combined answers -/

/-- Evaluation of the answer of cases 3 and 5 of `def:ld-combined-strategy`:
along a line contained in a fiber of the projection to the point coordinates,
the combining part of the point at parameter `t` is `α₀ + t w`, so the affine
answer built from the measured point answer `b` takes at `t` the combined
value of `b` at that point. -/
private theorem fiberAnswerEval (D : _root_.MIPStarRE.QPBT.DirectLdParams) (n : ℕ) (hn : 1 ≤ n)
    (z base dirn : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) (t : _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (ht : z = base + t • dirn) :
    _root_.MIPStarRE.QPBT.evalCoefficient
        (_root_.MIPStarRE.QPBT.coefficientsOfPolynomial n
          (_root_.MIPStarRE.QPBT.fiberLinePolynomial (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D base)
            (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D dirn) b)) t =
      ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D z r * b r := by
  have hz : _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D z =
      _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D base +
        t • _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    exact _root_.MIPStarRE.QPBT.directCombinedCoefficientPart_add_smul D base dirn t
  rw [_root_.MIPStarRE.QPBT.evalCoefficient_coefficientsOfPolynomial
      (le_trans (_root_.MIPStarRE.QPBT.fiberLinePolynomial_natDegree_le _ _ _) hn),
    _root_.MIPStarRE.QPBT.fiberLinePolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by simp

/-- Evaluation of the answer of case 2 of `def:ld-combined-strategy`: along an
axis-parallel line of the combined space with a point coordinate as stored
index, the combining part of the sampled point equals that of the canonical
base, and the shifted parameter presents the point part of the sampled point on
the measured line. -/
private theorem axisAnswerEval (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (z base dirn : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hdir : _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D dirn = 0) (s t : _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (f : Fin D.k → Fin (D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D) (c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hf : ∀ r, _root_.MIPStarRE.QPBT.evalCoefficient (f r) (t + s) = c r)
    (ht : z = base + t • dirn) :
    _root_.MIPStarRE.QPBT.evalCoefficient
        (_root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
          (_root_.MIPStarRE.QPBT.combinedAxisPolynomial (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D base) s f)) t =
      ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D z r * c r := by
  have hz : _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D z = _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D base := by
    conv_lhs => rw [ht]
    rw [_root_.MIPStarRE.QPBT.directCombinedCoefficientPart_add_smul, hdir, smul_zero, add_zero]
  rw [_root_.MIPStarRE.QPBT.evalCoefficient_coefficientsOfPolynomial
      (le_trans (_root_.MIPStarRE.QPBT.combinedAxisPolynomial_natDegree_le _ _ _)
        (le_of_eq (_root_.MIPStarRE.QPBT.DirectLdParams.combined_d D).symm)),
    _root_.MIPStarRE.QPBT.combinedAxisPolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by rw [hf]



/-! ## Structural clauses of the win predicate -/

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (q : _root_.MIPStarRE.QPBT.DirectLdQuestion D) {a b : _root_.MIPStarRE.QPBT.DirectLdAnswer D}
    (hwin : _root_.MIPStarRE.QPBT.directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer]









/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    {i : Fin D.combined.m} {j : Fin D.m}
    (h : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D i = Sum.inl j) :
    i = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (_root_.MIPStarRE.QPBT.directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inl j) := congrArg _ h
  rw [_root_.MIPStarRE.QPBT.directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    {i : Fin D.combined.m} {r : Fin D.k}
    (h : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D i = Sum.inr r) :
    i = _root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (_root_.MIPStarRE.QPBT.directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inr r) := congrArg _ h
  rw [_root_.MIPStarRE.QPBT.directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-! ## The acceptance clause on a point coordinate -/

/-- Case 2 of `def:ld-combined-strategy` at the parameter presenting the
sampled point: the affine shift `s` relating the two presentations of the image
line carries the acceptance clause of the original game at the shifted
parameter to the acceptance clause of the combined game. -/
theorem directCombinedAxisAnswer_eval (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (z dir : Fin D.combined.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hcoef : _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D dir = 0) (s T : _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hs : _root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.lineRepMap dir z) =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D dir)
          (_root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.lineRepMap dir z)) +
        s • _root_.MIPStarRE.QPBT.directCombinedPointPart D dir)
    (f : Fin D.k → Fin (D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D) (c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hT : z = _root_.MIPStarRE.QPBT.lineRepMap dir z + T • dir)
    (hcond : ∀ t : _root_.MIPStarRE.QPBT.DirectScalarQ D,
      _root_.MIPStarRE.QPBT.directCombinedPointPart D z =
          _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D dir) (_root_.MIPStarRE.QPBT.directCombinedPointPart D z) +
            t • _root_.MIPStarRE.QPBT.directCombinedPointPart D dir →
        ∀ r, _root_.MIPStarRE.QPBT.evalCoefficient (f r) t = c r) :
    _root_.MIPStarRE.QPBT.evalCoefficient
        (_root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
          (_root_.MIPStarRE.QPBT.combinedAxisPolynomial
            (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D (_root_.MIPStarRE.QPBT.lineRepMap dir z)) s f)) T =
      ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D z r * c r := by
  have hbase := _root_.MIPStarRE.QPBT.lineRepMap_directCombinedPointPart_lineRepMap D dir z
  have hpt : _root_.MIPStarRE.QPBT.directCombinedPointPart D z =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D dir) (_root_.MIPStarRE.QPBT.directCombinedPointPart D z) +
        (T + s) • _root_.MIPStarRE.QPBT.directCombinedPointPart D dir := by
    conv_lhs => rw [hT]
    rw [_root_.MIPStarRE.QPBT.directCombinedPointPart_add_smul, hs, hbase]
    module
  exact axisAnswerEval D z (_root_.MIPStarRE.QPBT.lineRepMap dir z) dir hcoef s T f c (hcond (T + s) hpt) hT



/-! ## The branch-wise acceptance transport -/



















end

end MIPStarRE.QPBT

/-!
# Branch-wise acceptance transport for the combined strategy

By `directRejectedMass_directCombinedStrategy_le`, the branch-wise estimates of
`lem:ld-combined-value` reduce to the following statement: the relabelling of
`def:ld-combined-strategy` sends an answer pair accepted by the win predicate
of the original game at the measured questions to an answer pair accepted by
the win predicate of the combined game.  This module proves that statement for
each of the nine ordered type pairs of the combined game.

Three of the nine branches are deterministic.  The two questions of a branch
whose type pair is diagonal are equal, so the acceptance clause of the original
game forces the two measured outcomes to be equal, and the relabelling, being a
function, sends them to equal combined outcomes.  The two branches pairing an
axis-parallel line with a diagonal line impose no condition in either game.

The six remaining branches pair a line with a point, and split according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  On a point coordinate the acceptance clause of the
combined game is obtained from the acceptance clause of the original game by
the affine change of parameter `directCombinedRebaseParameter`: the parameter
presenting the sampled point on the sampled line of the combined space presents
the point part of the sampled point on the image line, after the shift.  On a
combining coordinate the sampled line lies in a fiber of the projection to the
point coordinates, the combining part of the sampled point is the affine
function `α₀ + t w` of the parameter, and the acceptance clause of the combined
game is the identity `∑ r (α₀ + t w)_r b_r = ∑ r α_r b_r`.

All declarations below are formalization-only support for
`lem:ld-combined-value`; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## The two parts of a point along a line -/







/-! ## Degree bounds at the combined parameters -/





/-! ## Evaluation of the combined answers -/







/-! ## Structural clauses of the win predicate -/















/-! ## The acceptance clause on a point coordinate -/





/-! ## The branch-wise acceptance transport -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace D.combined) :
    _root_.MIPStarRE.QPBT.DirectCombinedWinTransport D .aline .point sample := by
  intro a b hwin
  rcases hsplit : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = _root_.MIPStarRE.QPBT.combinedPointVar D.m D.k j :=
      _root_.MIPStarRE.QPBT.eq_combinedPointVar_of_indexSplit D hsplit
    rw [_root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar D .aline j sample hindex,
      _root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a with
    | pointVals _ => simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
    | dlinePolys _ => simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
    | alinePolys f =>
      cases b with
      | alinePolys _ => simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
      | dlinePolys _ => simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
      | pointVals c =>
        have hsplitL : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D
            (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).index = Sum.inl j := hsplit
        have hcond : _root_.MIPStarRE.QPBT.directAlinePointCondition D
            (_root_.MIPStarRE.QPBT.directLdMap D .aline (_root_.MIPStarRE.QPBT.directCombinedSampleProjection D j sample))
            (_root_.MIPStarRE.QPBT.directLdMap D .point (_root_.MIPStarRE.QPBT.directCombinedSampleProjection D j sample))
            f c := by
          simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hwin
        have hdirpt : _root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) =
            _root_.MIPStarRE.QPBT.coordinateDirection j := by
          rw [hindex]
          exact _root_.MIPStarRE.QPBT.directCombinedPointPart_coordinateDirection_pointVar D j
        have hcoef : _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
            (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) = 0 := by
          rw [hindex]
          exact _root_.MIPStarRE.QPBT.directCombinedCoefficientPart_coordinateDirection_pointVar D j
        have hmdir : _root_.MIPStarRE.QPBT.directCombinedMeasuredDirection D
            (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) =
            _root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) := by
          simp only [_root_.MIPStarRE.QPBT.directCombinedMeasuredDirection, _root_.MIPStarRE.QPBT.directLdMap, hindex,
            _root_.MIPStarRE.QPBT.directCombinedIndexSplit_combinedPointVar,
            _root_.MIPStarRE.QPBT.directCombinedPointPart_coordinateDirection_pointVar]
        have hs : _root_.MIPStarRE.QPBT.directCombinedPointPart D
              (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) sample.point) =
            _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.coordinateDirection sample.index))
                (_root_.MIPStarRE.QPBT.directCombinedPointPart D
                  (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) sample.point)) +
              _root_.MIPStarRE.QPBT.directCombinedRebaseParameter D
                  (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) •
                _root_.MIPStarRE.QPBT.directCombinedPointPart D (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) := by
          rw [← hmdir]
          exact _root_.MIPStarRE.QPBT.directLineRepParameter_spec _ _
        have hgoal : _root_.MIPStarRE.QPBT.directAlinePointCondition D.combined
            (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample)
            (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample)
            (fun _ => _root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
                (_root_.MIPStarRE.QPBT.combinedAxisPolynomial
                  (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
                    (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).point)
                  (_root_.MIPStarRE.QPBT.directCombinedRebaseParameter D
                    (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample)) f))
            (fun _ => ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
              (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample).point r * c r) := by
          intro T hT _
          refine _root_.MIPStarRE.QPBT.directCombinedAxisAnswer_eval D sample.point
            (_root_.MIPStarRE.QPBT.coordinateDirection sample.index) hcoef _ T hs f c hT ?_
          rw [hdirpt]
          exact hcond
        have hmapA : _root_.MIPStarRE.QPBT.directCombinedAnswerMap D
            (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) (.alinePolys f) =
            .alinePolys (fun _ => _root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
                (_root_.MIPStarRE.QPBT.combinedAxisPolynomial
                  (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
                    (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).point)
                  (_root_.MIPStarRE.QPBT.directCombinedRebaseParameter D
                    (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample)) f)) := by
          simp only [_root_.MIPStarRE.QPBT.directCombinedAnswerMap, hsplitL]
        have hmapB : _root_.MIPStarRE.QPBT.directCombinedAnswerMap D
            (_root_.MIPStarRE.QPBT.LdType.point, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample) (.pointVals c) =
            .pointVals (fun _ => ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
              (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample).point r * c r) := rfl
        rw [hmapA, hmapB]
        simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hgoal
  · have hindex : sample.index = _root_.MIPStarRE.QPBT.combinedCoefficientVar D.m D.k r₀ :=
      _root_.MIPStarRE.QPBT.eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [_root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex,
      _root_.MIPStarRE.QPBT.directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    have hab : a = b := _root_.MIPStarRE.QPBT.directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
    | dlinePolys _ =>
      simp [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.directLdPointQuestionOf, _root_.MIPStarRE.QPBT.validDirectLdAnswer] at hwin
    | pointVals bv =>
      have hsplitL : _root_.MIPStarRE.QPBT.directCombinedIndexSplit D
          (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).index = Sum.inr r₀ := hsplit
      have hgoal : _root_.MIPStarRE.QPBT.directAlinePointCondition D.combined
          (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample)
          (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample)
          (fun _ => _root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
              (_root_.MIPStarRE.QPBT.fiberLinePolynomial
                (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).point)
                (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
                  (_root_.MIPStarRE.QPBT.directCombinedQuestionDirection D (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined
                    _root_.MIPStarRE.QPBT.LdType.aline sample))) bv))
          (fun _ => ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
            (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample).point r * bv r) := by
        intro T hT _
        exact fiberAnswerEval D D.combined.d D.hd
          (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample).point
          (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).point
          (_root_.MIPStarRE.QPBT.directCombinedQuestionDirection D (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline
            sample)) bv T hT
      have hmapA : _root_.MIPStarRE.QPBT.directCombinedAnswerMap D
          (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample) (.pointVals bv) =
          .alinePolys (fun _ => _root_.MIPStarRE.QPBT.coefficientsOfPolynomial D.combined.d
              (_root_.MIPStarRE.QPBT.fiberLinePolynomial
                (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.aline sample).point)
                (_root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
                  (_root_.MIPStarRE.QPBT.directCombinedQuestionDirection D (_root_.MIPStarRE.QPBT.LdType.aline, _root_.MIPStarRE.QPBT.directLdMap D.combined
                    _root_.MIPStarRE.QPBT.LdType.aline sample))) bv)) := by
        simp only [_root_.MIPStarRE.QPBT.directCombinedAnswerMap, hsplitL]
      have hmapB : _root_.MIPStarRE.QPBT.directCombinedAnswerMap D
          (_root_.MIPStarRE.QPBT.LdType.point, _root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, _root_.MIPStarRE.QPBT.directCombinedCoefficientPart D
            (_root_.MIPStarRE.QPBT.directLdMap D.combined _root_.MIPStarRE.QPBT.LdType.point sample).point r * bv r) := rfl
      rw [hmapA, hmapB]
      simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hgoal
