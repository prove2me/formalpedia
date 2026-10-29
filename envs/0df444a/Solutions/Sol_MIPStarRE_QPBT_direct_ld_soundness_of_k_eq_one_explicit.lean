-- Prove2me | solution 1 for MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:58:15.06873+00:00
-- url     : https://prove2.me/submissions/32550e4a-71fa-49f9-a5b3-c4a1a7b8021f

-- Generated proof for MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_State
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Error
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormal
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_deltaLd_of_transportBound
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_outcome_equiv
import Theorems.Thm_MIPStarRE_QPBT_directCoordinate_failure_le_three_mul_rejection
import Theorems.Thm_MIPStarRE_QPBT_directLdRejectionProbability_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_directLdtPointNonempty
import Theorems.Thm_MIPStarRE_QPBT_directPointPolynomial_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_directPolynomialPoint_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_directPolynomialPolynomial_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_direct_ld_transport_constants_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Soundness.lean. -/
/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section



/-! ## Absorbing the error bound from the low individual degree theorem

The specializations below combine three inputs: polynomial-tuple conclusions
whose error is built from `mainFormalError`, the error bound of
`thm:main-formal` at the auxiliary sampling parameter; the absorption
`exists_directLdTransportConstants` of that error into `deltaLd`; and the
coarse bound `consistencyDefect_heteroKron_le_one`, which closes both the
regime `1 ≤ ε` and the regime where the transport argument exceeds one, in
each of which `deltaLd` is already at least one. -/

/-- Formalization-only scalar step: a quantity dominated by an argument that
is itself at most one is dominated by the square root of that argument.

Support for the transport of `lem:ld-soundness`, blueprint
`ch13_qpbt_test.tex:139-167`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem le_sqrt_of_le_of_le_one {x T : ℝ} (hxT : x ≤ T) (hT : T ≤ 1) :
    x ≤ Real.sqrt T := by
  rcases le_or_gt x 0 with hx | hx
  · exact le_trans hx (Real.sqrt_nonneg T)
  · have hx2 : x ^ 2 ≤ T := by nlinarith
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx.le).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hx2











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Error.lean. -/
/-!
# The scalar error of the low-degree soundness transport

This module supplies the scalar half of the soundness transport for the
directly indexed low-degree game.  Its content is purely arithmetic: the
auxiliary sampling parameter with which the low individual degree theorem is
applied to a coordinate strategy, the resulting bounds on the three terms of
the LDT error `mainFormalError`, and the absorption of the
simultaneous-measurement estimate into the error function `deltaLd` of
`lem:ld-soundness`.

## Main definitions

* `directLdAuxParameter D = 2560000 m³ d` is the sampling parameter handed to
  `MIPStarRE.LDT.Test.mainFormal`.  It is the multiple of the exponential scale
  `2560000 m²` of `mainFormalError` with quotient `m d`, so that the
  exponential term of the LDT error is exactly `exp (-m d)`.

## Main results

* `directLdAuxParameter_pos` and `four_hundred_mul_le_directLdAuxParameter` are
  the two hypotheses `0 < k` and `400 m d ≤ k` of `mainFormal`, proved from the
  positivity of the dimension and of the degree alone.
* `directLd_test_term_le`, `directLd_field_term_le` and
  `directLd_exponential_term_le` bound the three terms of
  `mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 ε)`: the test
  term by `3 ε^(1/40000)`, the field term by `d q^(-1/40000)`, and the
  exponential term by `2^(-b m d)` for every `0 ≤ b ≤ 1`.
* `exists_directLdTransportConstants` exhibits, for a sandwich constant
  `C₀ ≥ 1`, the explicit universal constants `a = 2500000000 C₀` and
  `b = 1/80000` for which `C₀ k √(mainFormalError + m d / q + ε)` is at most
  `deltaLd a b ε q m d k` in the regime `0 < ε ≤ 1`.
* `one_le_deltaLd_of_one_le_error` and
  `one_le_deltaLd_of_fieldSize_le_degree` bound `deltaLd` below by one in the
  two degenerate regimes `1 ≤ ε` and `q ≤ d`, and
  `consistencyDefect_heteroKron_le_one` bounds every bipartite consistency
  defect on a unit state above by one.  Together they close both degenerate
  regimes, where the conclusion of `lem:ld-soundness` carries no information.

The exponent `b = 1/80000` is half the exponent `1/40000` carried by
`mainFormalError`; the halving is exactly what the square root of the
simultaneous-measurement estimate costs.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:139-167`
* `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:288-327`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
* `references/ldt-paper/test_definition.tex:180-202`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

/-! ## The auxiliary sampling parameter -/



/-- The auxiliary sampling parameter is positive, which is the boundary
hypothesis `0 < k` of `MIPStarRE.LDT.Test.mainFormal`. -/
theorem directLdAuxParameter_pos (D : _root_.MIPStarRE.QPBT.DirectLdParams) : 0 < _root_.MIPStarRE.QPBT.directLdAuxParameter D := by
  have hm : 0 < D.m := D.hm
  have hd : 0 < D.d := D.hd
  have hpow : 0 < D.m ^ 3 := pow_pos hm 3
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hpow) hd

/-- The auxiliary sampling parameter satisfies the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal`, documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`. -/
theorem four_hundred_mul_le_directLdAuxParameter (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    400 * D.toLDTParameters.m * D.toLDTParameters.d ≤ _root_.MIPStarRE.QPBT.directLdAuxParameter D := by
  have hcube : D.m ≤ D.m ^ 3 := Nat.le_self_pow (by norm_num) D.m
  change 400 * D.m * D.d ≤ 2560000 * D.m ^ 3 * D.d
  exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hcube) le_rfl

/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/









/-! ## The three terms of the LDT error -/









/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/









/-! ## The LDT error at the auxiliary sampling parameter -/













/-! ## Absorption into the error function of `lem:ld-soundness` -/





/-! ## The degenerate regimes

In the two regimes `1 ≤ ε` and `q ≤ d` the error function `deltaLd` is at
least one, so the consistency conclusions of `lem:ld-soundness` hold for any
witnesses; the low-degree test carries no information there. -/





/-! ## A coarse universal bound on the consistency defect

The consistency defect compared with `deltaLd` in `lem:ld-soundness` is the
off-diagonal Born mass of a pair of measurement families acting on the two
tensor factors of a unit bipartite state.  Since the joint Born weights are
nonnegative and sum to one, that mass is at most one; combined with the two
lower bounds on `deltaLd` above this closes the regimes `1 ≤ ε` and `q ≤ d`.

The theorem below is formalization-only.  It is a generic statement about
`consistencyDefect` rather than about the low-degree game, and would naturally
live in `MIPStarRE/QPBT/Games/DistanceTheorems.lean`. -/



end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/PassConversion.lean. -/
/-!
# Pass conversion for the directly indexed low-degree game

This module converts a value bound for a projective strategy of the directly
indexed low-degree game into the hypothesis of the low individual degree
theorem for each coordinate strategy `directCoordinateProjStrat`.

The LDT failure probability gives weight `1/3` to point agreement and
`1/6` to each of the four oriented line-versus-point checks.  The branch
comparisons of `Transport.BranchComparison` and `Transport.DiagonalRecursion`
bound the point and axis-line branches by the corresponding direct branch
rejections and each diagonal branch by twice its direct branch rejection.  The
factor-three rejection calculus of `GameValue` gives the line branches half the
weight of the point branch, so the factor two is absorbed: a direct strategy of
value at least `1 - ε` has coordinate strategies of LDT failure at most
`3 * ε`, which is exactly `PassesLowIndividualDegreeTest (3 * ε)`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300-311`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The failure comparison and the pass hypothesis -/











/-- A direct strategy of value at least `1 - ε` has coordinate strategies of
low individual degree failure at most `3 * ε`. -/
theorem directCoordinate_failure_le_three_mul_error
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
      3 * ε := by
  letI := D.toLDTFieldModel
  have hrej : _root_.MIPStarRE.QPBT.directLdRejectionProbability D S ≤ ε := by
    rw [_root_.MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value]
    linarith
  calc
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).lowIndividualDegreeFailureProbability ≤
        3 * _root_.MIPStarRE.QPBT.directLdRejectionProbability D S :=
      _root_.MIPStarRE.QPBT.directCoordinate_failure_le_three_mul_rejection D S hS r
    _ ≤ 3 * ε := by linarith

/-- The pass hypothesis of the low individual degree theorem for every
coordinate of a direct strategy of value at least `1 - ε`, with error
`3 * ε` and no further assumption. -/
theorem directCoordinate_passes
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).PassesLowIndividualDegreeTest (3 * ε) := by
  letI := D.toLDTFieldModel
  exact ⟨_root_.MIPStarRE.QPBT.directCoordinate_failure_le_three_mul_error D S hS r ε hwin⟩

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Simultaneous.lean. -/
/-!
# Simultaneous polynomial measurements for the direct low-degree game

This module applies the quantum soundness theorem of the low individual
degree test to each coordinate of a projective strategy for the directly
indexed low-degree game, transports the Schwartz--Zippel collision estimate
to the direct polynomial representatives, and, for simultaneity parameter
`1`, obtains the polynomial-tuple conclusion of `lem:ld-soundness` from the
coordinate conclusions.

## The simultaneity obstruction

For simultaneity parameter `k ≥ 2` the coordinate conclusions alone do not
determine simultaneous polynomial measurements, so no palindromic combination
of the coordinate measurements can be consistent with a joint point
measurement in general.  Let `q = 2^s`, let the degree be `1`, and let Bob
measure the univariate polynomials `g = g₀ + g₁ x` once in the standard basis
`|g⟩` and once in the Fourier basis attached to the symmetric pairing
`⟨h, g⟩ = h₀ g₁ + h₁ g₀`.  In characteristic two every evaluation functional
`h ↦ h(u)` is represented by an isotropic vector of this pairing, so at every
point `u` the value-level coarse-grainings `Q^{1,u}_{[a]}` (Fourier basis) and
`Q^{2,u}_{[b]}` (standard basis) commute, and on the maximally entangled state
Alice may answer point questions with the joint projective measurement
`P^u_{a,b} = (Q^{1,u}_{[a]} Q^{2,u}_{[b]})ᵀ`.  All coordinate consistencies of
`lem:ld-soundness` then hold with defect `0` and distinct polynomials collide
at a uniform point with probability `1 / q`, but the sandwiched POVM has
`∑_{g₂(u) = b} |g₂⟩⟨g₂| Q^{1,u}_{[a]} |g₂⟩⟨g₂| = q⁻¹ Q^{2,u}_{[b]}`, whose
consistency defect against `P^u` is `1 - 1/q`; more strongly, every
polynomial-pair POVM on Bob's side has defect at least `1 - 2/q` against
`P^u`.  No bound of the form `C k √(δ + m d / q)` holds for a universal `C`.
The source obtains the general case not coordinatewise but by the combining
reduction of Theorem 4.43 in the NEEXP paper, which applies the `k = 1`
theorem once, in dimension `m + k`, to a combined strategy; that reduction is
not formalized here.  The two-measurement pasting estimate (Fact 4.35 there)
does not apply either, since it evaluates the two coordinates at
independently sampled points while the low-degree game evaluates all
coordinates at one point.  The counterexample and the resulting formal
status are recorded in `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`
* `references/neexp-paper/05_quantum_preliminaries.tex:912-1060` and `:1409-1503`
* `references/ldt-paper/test_definition.tex:180-202`
* `lem:ld-soundness` in `blueprint/src/chapter/ch13_qpbt_test.tex`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Direct polynomial collision estimate -/



/-! ## Coordinatewise low individual degree soundness -/

/-- Quantum soundness of the low individual degree test (`thm:main-formal`,
paper `references/ldt-paper/test_definition.tex:180-202`) applied to one
coordinate of a projective strategy for the direct low-degree game.

The coordinate strategy passes the test with failure probability at most
`3 ε`, and the theorem is instantiated at the auxiliary sampling parameter
`directLdAuxParameter D`; both numerical side conditions of the theorem follow
from the positivity of the dimension and of the degree.  Blueprint
`lem:ld-soundness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem directCoordinateMainFormal
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (ε : _root_.LIDT.MIPStarRE.LDT.Error)
    (hwin : 1 - ε ≤ S.value) :
    letI := D.toLDTFieldModel
    ∃ GA : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA,
      ∃ GB : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB,
        _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementA)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily D.toLDTParameters GB.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters
              (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε)) ∧
          _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily D.toLDTParameters GA.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
              (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementB)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters
              (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε)) ∧
          _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily GA.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily GB.toSubMeas)
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters
              (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε)) := by
  letI := D.toLDTFieldModel
  exact _root_.LIDT.MIPStarRE.LDT.Test.mainFormal D.toLDTParameters
    (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r) (3 * ε)
    (_root_.MIPStarRE.QPBT.directCoordinate_passes D S hS r ε hwin).soundnessHypothesis
    (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (_root_.MIPStarRE.QPBT.four_hundred_mul_le_directLdAuxParameter D)
    (_root_.MIPStarRE.QPBT.directLdAuxParameter_pos D)





/-! ## One-coordinate tuples -/

/-- Relabeling an outcome by a constant tuple over a one-element index set is
selected by the value of the tuple at the unique index. -/
private theorem const_tuple_eq_iff {iota beta : Type*} [Unique iota]
    (v : iota → beta) (b : beta) :
    v = (fun _ => b) ↔ v default = b :=
  funext_iff.trans Unique.forall_iff

/-- The effect of a tuple-relabeled measurement at a constant tuple over a
one-element index set is the effect of the relabeling by the unique
coordinate. -/
private theorem postprocess_effect_const_tuple
    {alpha beta iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype iota] [DecidableEq iota]
    [Unique iota] [Fintype d] [DecidableEq d]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha d) (f : alpha → iota → beta) (b : beta) :
    (M.postprocess f).effect (fun _ => b) =
      (M.postprocess (fun a => f a default)).effect b := by
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Finset.sum_congr
    (Finset.filter_congr fun a _ => const_tuple_eq_iff (f a) b)
    (fun _ _ => rfl)

/-- Reading a measurement as a one-coordinate tuple measurement does not
change its effects. -/
private theorem postprocess_const_tuple_effect_self
    {alpha iota d : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype iota] [DecidableEq iota] [Unique iota] [Fintype d] [DecidableEq d]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha d) (p : alpha) :
    (M.postprocess (fun a (_ : iota) => a)).effect (fun _ => p) = M.effect p := by
  rw [postprocess_effect_const_tuple]
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.filter_eq',
    Finset.mem_univ, if_true, Finset.sum_singleton]

/-- Transport one-coordinate polynomial measurements to singleton tuples
without changing any of the three consistency bounds. -/
private theorem direct_coordinate_measurements_to_tuple_of_k_eq_one
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (hk : D.k = 1) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) (bound : ℝ)
    (hcoord :
      letI := D.toLDTFieldModel
      ∃ GA₀ : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA,
        ∃ GB₀ : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB,
          _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
              (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
                (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementA)
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily D.toLDTParameters GB₀.toSubMeas) bound ∧
            _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
              (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily D.toLDTParameters GA₀.toSubMeas)
              (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas
                (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementB) bound ∧
            _root_.LIDT.MIPStarRE.LDT.ConsRel (_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
              (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily GA₀.toSubMeas)
              (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily GB₀.toSubMeas) bound) :
    ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
      ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron
                (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron 1
                ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤ bound ∧
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron
                ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron 1
                (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤ bound ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g)) S.ψ ≤ bound := by
  letI := D.toLDTFieldModel
  haveI hU : Unique (Fin D.k) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.isLt; omega) }
  have hr : r = default := Subsingleton.elim _ _
  subst r
  obtain ⟨GA₀, GB₀, h1, h2, h3⟩ := hcoord
  refine ⟨(_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GA₀).postprocess (fun g _ => g),
    (_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GB₀).postprocess (fun g _ => g), ?_, ?_, ?_⟩
  · have h1' := _root_.MIPStarRE.QPBT.directPointPolynomial_consistencyDefect_le D S hS default GB₀ _ h1
    refine ((_root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (_root_.MIPStarRE.QPBT.DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h1'
    · intro u a
      change _root_.MIPStarRE.QPBT.heteroKron (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect (fun _ => a)) 1 = _
      rw [postprocess_effect_const_tuple]
      rfl
    · intro u a
      change _root_.MIPStarRE.QPBT.heteroKron 1 ((((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GB₀).postprocess
        (fun g _ => g)).postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect
          (fun _ => a)) = _
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
  · have h2' := _root_.MIPStarRE.QPBT.directPolynomialPoint_consistencyDefect_le D S hS default GA₀ _ h2
    refine ((_root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (_root_.MIPStarRE.QPBT.DirectScalarQ D)).symm _ _ S.ψ).symm.trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h2'
    · intro u a
      change _root_.MIPStarRE.QPBT.heteroKron ((((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GA₀).postprocess
        (fun g _ => g)).postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect
          (fun _ => a)) 1 = _
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
        postprocess_effect_const_tuple]
      rfl
    · intro u a
      change _root_.MIPStarRE.QPBT.heteroKron 1 (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect (fun _ => a)) = _
      rw [postprocess_effect_const_tuple]
      rfl
  · have h3' := _root_.MIPStarRE.QPBT.directPolynomialPolynomial_consistencyDefect_le D S GA₀ GB₀ _ h3
    refine ((_root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv _
      (Equiv.funUnique (Fin D.k) (_root_.MIPStarRE.QPBT.PolyIndex D.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d)).symm _ _
        S.ψ).symm.trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ ?_ ?_)).trans_le h3'
    · intro _ p
      change _root_.MIPStarRE.QPBT.heteroKron (((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GA₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) 1 = _
      rw [postprocess_const_tuple_effect_self]
    · intro _ p
      change _root_.MIPStarRE.QPBT.heteroKron 1 (((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GB₀).postprocess
        (fun g _ => g)).effect (fun _ => p)) = _
      rw [postprocess_const_tuple_effect_self]

/-- The polynomial-tuple conclusion of `lem:ld-soundness` for simultaneity
parameter `1`: the coordinate conclusions of the low individual degree
theorem, read as one-coordinate tuples.

The three consistency defects carry the error of `thm:main-formal` at the
auxiliary parameter `directLdAuxParameter D` and pass bound `3 ε`; its
absorption into the error function `deltaLd` is
`exists_directLdTransportConstants`.  For simultaneity parameter at least `2`
the coordinate conclusions do not determine simultaneous polynomial
measurements; see the module docstring and
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.  Blueprint
`lem:ld-soundness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directSimultaneousPolynomialMeasurements_of_k_eq_one
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (hk : D.k = 1) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (ε : _root_.LIDT.MIPStarRE.LDT.Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
      ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron
                (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron 1
                ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) ∧
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron
                ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome =>
              _root_.MIPStarRE.QPBT.heteroKron 1
                (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                  (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
            S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) := by
  apply direct_coordinate_measurements_to_tuple_of_k_eq_one D hk S hS ⟨0, D.hk⟩ _
  letI := D.toLDTFieldModel
  exact _root_.MIPStarRE.QPBT.directCoordinateMainFormal D S hS ⟨0, D.hk⟩ ε hwin





end

end MIPStarRE.QPBT

/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum





/-! ## Absorbing the error bound from the low individual degree theorem

The specializations below combine three inputs: polynomial-tuple conclusions
whose error is built from `mainFormalError`, the error bound of
`thm:main-formal` at the auxiliary sampling parameter; the absorption
`exists_directLdTransportConstants` of that error into `deltaLd`; and the
coarse bound `consistencyDefect_heteroKron_le_one`, which closes both the
regime `1 ≤ ε` and the regime where the transport argument exceeds one, in
each of which `deltaLd` is already at least one. -/

theorem solution :
    ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
            ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
                    _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower ε D.q D.m D.d D.k := by
  let a := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
  let b := _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
  obtain ⟨ha₀, hb₀, _hb1, habs₀⟩ := _root_.MIPStarRE.QPBT.direct_ld_transport_constants_explicit 1 le_rfl
  have ha : 1 ≤ a := by
    simpa only [a, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant, mul_one] using ha₀
  have hb : 0 < b := by
    simpa only [b, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower] using hb₀
  have habs : ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
      1 * (D.k : ℝ) *
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
        _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k := by
    simpa only [a, b, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower,
      mul_one] using habs₀
  intro D ε hk hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    _root_.MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D hk S hS ε hwin
  have hmd : (0 : ℝ) ≤ ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) := by positivity
  have hmature : ∀ hT :
      _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
          ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε ≤ 1,
      _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) ≤
        Real.sqrt
          (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
    intro hT
    exact _root_.MIPStarRE.QPBT.le_sqrt_of_le_of_le_one (by linarith) hT
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  · refine _root_.MIPStarRE.QPBT.consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (fun u => (S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D))
      (fun u => GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h1 (hmature hT)
  · refine _root_.MIPStarRE.QPBT.consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (fun u => GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u))
      (fun u => (S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h2 (hmature hT)
  · refine _root_.MIPStarRE.QPBT.consistencyDefect_le_deltaLd_of_transportBound ha hb le_rfl habs D ε hε
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (fun _ => GA) (fun _ => GB) S.ψ S.ψ_norm ?_
    intro _ hT
    rw [one_mul]
    exact le_trans h3 (hmature hT)
