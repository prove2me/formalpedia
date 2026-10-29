-- Prove2me | solution 1 for MIPStarRE.QPBT.marginal_eval_overlap_le_decoded_add_nonencoding_prime
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:48:41.572595+00:00
-- url     : https://prove2.me/submissions/7f5ad3a2-80c7-4738-92d0-ffc04c5e7635

-- Generated proof for MIPStarRE.QPBT.marginal_eval_overlap_le_decoded_add_nonencoding'.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm

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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Algebra/Decoding.lean. -/
/-! # Polynomial decoding for Pauli extraction

This module provides the Chapter 16 decoder on the Chapter 15 bounded
polynomial representative type.  The generic retained-value decoder and its
specialization to polynomial representatives live in
`Algebra/LowDegreeCodeTheorems`; this module states the corresponding maps on
`Poly P` used in the extraction chapter.

## References

The decoder is blueprint `def:decoding-map`, with its extraction use in
blueprint `sec:separating` and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1419-1450`.
The restricted decoder identity and its encoding hypothesis are documented in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries

/-! ## Representative evaluation and decoding -/









/-! ## The encoding image -/







/-! ## Decoder companions -/







/-- Decoder/evaluation agreement for an encoding representative only.

The hypothesis `hg : IsEncoding g` is mandatory.  For a general bounded
polynomial, Boolean-cube values determine its multilinear interpolant, which
need not equal the original representative.  This is the corrected form of
the source step at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`;
see `docs/paper-gaps/qpbt_decoding-identity.tex:87-123`.

**Local fix:** The source's unrestricted identity is false, as witnessed by
`g(x) = x^2` over a field with more than two elements.  The encoding restriction
and representative semantics are documented in
`docs/paper-gaps/qpbt_decoding-identity.tex:87-123`. -/
theorem decodeFq_dotProduct_indicatorVec {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {g : _root_.MIPStarRE.QPBT.Poly P} (hg : _root_.MIPStarRE.QPBT.IsEncoding g) (x : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) (_root_.MIPStarRE.QPBT.indicatorVec x) = _root_.MIPStarRE.QPBT.evalPoly g x := by
  unfold _root_.MIPStarRE.QPBT.IsEncoding at hg
  calc
    dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) (_root_.MIPStarRE.QPBT.indicatorVec x) = _root_.MIPStarRE.QPBT.lowDegreeEnc (_root_.MIPStarRE.QPBT.decodeFq g) x :=
      (_root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) x).symm
    _ = _root_.MIPStarRE.QPBT.evalPoly g x := by simp [_root_.MIPStarRE.QPBT.lowDegreeEnc, _root_.MIPStarRE.QPBT.evalPoly, hg]

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/ConsistencyPositivity.lean. -/
/-!
# Positivity of the consistency defect on opposite placements

The error-inflation estimates for restricted line distributions apply to
nonnegative averages.  This module supplies the missing nonnegativity: the
integrand of `consistencyDefect` for two complete measurements placed on
opposite registers is a state quadratic form of a positive operator.  Indeed,
after separating the two placements along the corresponding tensor
bipartition, the off-diagonal sum is
`∑_a (place p₁ E_a) (place p₂ (∑_{b ≠ a} F_b))`, a sum of products of
positive operators supported on complementary registers.  The placement
algebra itself — additivity, the image of zero, positivity and the commutation
of opposite placements — is supplied by the placement identities proved in
`MIPStarRE.QPBT.Combining.Points.PlacementSupport` and
`MIPStarRE.QPBT.Observables.LineMeasurement.LinePointOverlap`.

## References

The consistency defect is blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.  The
placements and their bipartitions are blueprint `def:expanded-state`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
nonnegativity is the hypothesis of items 1 and 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-- Positive operators placed on a directed opposite pair of registers have a
positive product.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_mul_place_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement) (hopp : p₁.IsOpposite p₂)
    {X : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₁.side)}
    {Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y := by
  exact Commute.mul_nonneg (S.place_nonneg p₁ hX) (S.place_nonneg p₂ hY)
    (S.place_comm p₁ p₂ hopp X Y)





end ProjectiveSetting

/-! ## Nonnegativity of the pointwise consistency defect -/





end

end MIPStarRE.QPBT

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

/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}

open scoped Classical in

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
    (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
      (S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (MvPolynomial.eval u g.1)))) ≤
      (∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect
            (dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) (_root_.MIPStarRE.QPBT.indicatorVec u))))) +
      ∑ g ∈ Finset.univ.filter (fun g : _root_.MIPStarRE.QPBT.Poly P => ¬ _root_.MIPStarRE.QPBT.IsEncoding g),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
  classical
  have hpos (g : _root_.MIPStarRE.QPBT.Poly P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
      0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg _ (S.place_mul_place_nonneg .AA' .BA'' (by trivial)
      ((w.marginalPoly .alice W).pos g) ((S.pointMeasExp .bob W u).pos a))
  have hsum (g : _root_.MIPStarRE.QPBT.Poly P) :
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect a))) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
    have hc : (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
        S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) = 1 :=
      (S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)).sum_eq_one
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← Finset.mul_sum, hc, mul_one]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : _root_.MIPStarRE.QPBT.IsEncoding g
  · simp only [hg, not_true_eq_false, if_false, add_zero]
    rw [_root_.MIPStarRE.QPBT.decodeFq_dotProduct_indicatorVec hg u]
    rfl
  · simp only [hg, not_false_eq_true, if_true]
    have hle := Finset.single_le_sum (fun a _ => hpos g a)
      (Finset.mem_univ (MvPolynomial.eval u g.1))
    rw [hsum] at hle
    exact hle.trans (le_add_of_nonneg_left (hpos g _))
