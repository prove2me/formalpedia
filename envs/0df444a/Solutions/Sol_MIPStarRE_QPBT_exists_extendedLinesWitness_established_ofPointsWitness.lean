-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_extendedLinesWitness_established_ofPointsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:47:10.610023+00:00
-- url     : https://prove2.me/submissions/8d8b4420-62c0-463a-b6ce-add0bf511fcd

-- Generated proof for MIPStarRE.QPBT.exists_extendedLinesWitness_established_ofPointsWitness.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Overlap
import Definitions.Def_QPBT_QPBT_Combining_Lines_CombinedMeasurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_expLineOp_zero_of_not_deg_d
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_extendedMeasurement_axis_degree
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_extended_consistencyDefect_le
import Theorems.Thm_MIPStarRE_QPBT_combined_line_measurement_consistency
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_le_one
import Theorems.Thm_MIPStarRE_QPBT_exists_combining_polynomial_bound
import Theorems.Thm_MIPStarRE_QPBT_exists_subLineWitness
import Theorems.Thm_MIPStarRE_QPBT_subline_joint_overlap_near_one_at_explicit

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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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





























/-! ## Finite direct-line carrier -/

































/-- The directly indexed axis-line/point law is probabilistic. -/
theorem directALinePointDist_isProbability (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directALinePointDist D).IsProbability := by
  exact (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability (_root_.MIPStarRE.QPBT.DirectLdSpace D)).map _

/-- The directly indexed diagonal-line/point law is probabilistic. -/
theorem directDLinePointDist_isProbability (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directDLinePointDist D).IsProbability := by
  exact (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability (_root_.MIPStarRE.QPBT.DirectLdSpace D)).map _

/-- The directly indexed line-point mixture is probabilistic. -/
theorem directLinePointDist_isProbability (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directLinePointDist D).IsProbability := by
  exact _root_.MIPStarRE.QPBT.Distribution.mix_isProbability _ _ _
    (_root_.MIPStarRE.QPBT.directALinePointDist_isProbability D) (_root_.MIPStarRE.QPBT.directDLinePointDist_isProbability D)
    (by norm_num) (by norm_num)











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLines/Estimates.lean. -/
/-!
# Estimates for the extended-line construction

This construction uses the directly indexed extended-line space, the answer
alphabet obtained from the field by adjoining an undefined-evaluation outcome,
and the corrected sum-form convention for polynomial errors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section













/-- A universal constant bounds the deviation of the paired subline overlap from
one in terms of the point, line, and strategy errors. -/
theorem subline_joint_overlap_near_one_at :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error pointError lineError : ℝ)
        (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError)
        (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness setting points lineError) (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params)
        (first second : _root_.MIPStarRE.QPBT.Placement), first.IsOpposite second →
        |avgOver sublines.D (_root_.MIPStarRE.QPBT.pairedSublineOverlap setting points lines first second) - 1| ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := by
  exact ⟨6, by norm_num, _root_.MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit⟩


end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/CombinedMeasurement.lean. -/
/-!
# Combined X/Z line measurement

This module constructs the X-Z-X sandwich POVM used to combine one X-line
measurement with one Z-line measurement.  It also records the orientation of
the sandwich as a one-sided pasted measurement and the two axis-degree support
properties.

## References

The construction is the paired-line measurement in `lem:qld-xz-lines`, with
source `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:942-949`.
Its separate blueprint entries are `def:concrete-paired-line-measurement` and
`lem:concrete-paired-line-degree-support`; consistency remains the distinct
obligation `lem:combined-line-measurement-consistency`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section







/-- The X-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_X
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (fX fZ : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineX.kind = .axis) (hf : ¬ fX.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .X lineX haxis fX hf, zero_mul]

/-- The Z-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_Z
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (lineX lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (fX fZ : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineZ.kind = .axis) (hf : ¬ fZ.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .Z lineZ haxis fZ hf, mul_zero, zero_mul]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines.lean. -/
/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Combined line measurements -/


/-- Conditional joint X/Z line measurements for a polynomially controlled
point-witness family supporting `lem:qld-xz-lines`.

**Conditional auxiliary supporting:** blueprint
`lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
The matching conditional blueprint entry is `lem:combined-lines-given-points`.
The error depends polynomially on `ε` and `md/q`, and the witness retains all
directed opposite-placement comparisons. This formalization-only conditional form
takes the supplied point-error function `deltaQ` and its bound `hdeltaQ : IsPolyErr deltaQ`
before choosing the line-error function. It also assumes a supplied point witness
`points : CombinedPointsWitness S (deltaQ ε)` at strategy error `ε`.
The separate source-facing declaration `exists_combinedLinesWitness` supplies
the point-error function, its bound, and the point witness existentially.
The comparisons here use the completed answer alphabet; the conditional entry
does not certify the source comparison on field-valued answers.

**Domain repair (issue Dengnifer/MIPStarRE-QPBT-bak#389):** The former statement quantified an
arbitrary
scalar point error after choosing `deltaP`, although the pasting estimate depends
on that point error.  The repaired domain matches the point family supplied by
`exists_combinedPointsWitness`.  The source-facing theorem below still supplies
that family existentially and has an unchanged statement.  The obstruction and
the named construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The witness below uses `S.combinedLineMeasurement` explicitly. Its consistency
is proved by the point-to-line comparisons and pasting construction; see
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#414.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue
Dengnifer/MIPStarRE-QPBT-bak#196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness_ofPointsWitness (deltaQ : ℝ -> ℝ)
    (hdeltaQ : _root_.MIPStarRE.QPBT.IsPolyErr deltaQ) :
    ∃ deltaP : ℝ -> ℝ -> ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ deltaP ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S (deltaQ ε)),
        Nonempty (_root_.MIPStarRE.QPBT.CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaP, hdeltaP, hconsistent⟩ :=
    _root_.MIPStarRE.QPBT.combined_line_measurement_consistency deltaQ hdeltaQ
  refine ⟨deltaP, hdeltaP, ?_⟩
  intro P ε S points
  exact ⟨{ T := S.combinedLineMeasurement
           axis_degree_X := S.combinedLineMeasurement_axis_degree_X
           axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
           consistent := hconsistent P ε S points }⟩



/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form for a supplied polynomially controlled point family. -/



/-! ## Restricted line distributions -/











/-! ## The sub-line distribution -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/SelfConsistency.lean. -/
/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

The module also records that the error parameter of a projective setting is
nonnegative, which is not assumed by the structure and is needed by the other
two items as well.

## References

The declarations formalize `enu:qld-comm-line-self-cons`, item 1 of
`lem:qld-comm-line-cons`, whose paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Self-consistency of the unexpanded line measurements -/











namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The error parameter -/

/-- The error parameter of a projective setting is nonnegative. Nothing in the
structure assumes this: it follows from the winning premise `1 - ε ≤ value`
together with the bound `value ≤ 1` satisfied by the value of every strategy.
Formalization-only auxiliary supplying the sign condition of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : 0 ≤ ε := by
  have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
  have hw := S.win
  linarith

/-! ## Placement of differences on the two bipartitions -/

-- The four-level product indices below exceed the default instance-search
-- size.







/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/













end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Applying the classical low-degree test

This module states the two application obligations at the end of the Pauli-basis
combining argument.  Directly indexed combined-line measurements are recorded both
with the error form printed in the source, as an unasserted proposition, and with
the weaker estimate established by its first proof route, as a theorem.  The
final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials.  The existence assertions below
record the measurements and quantitative estimates required by the combining argument.
The established direct-line constructor, its conditional supplied-point companion,
and the source global-pair theorem are proved.  The printed error form of the
combined-line lemma remains an open source gap, tracked by issue Dengnifer/MIPStarRE-QPBT-bak#598;
it is
recorded here as a proposition that is stated but not asserted, so this module
contains no proof debt.

## References

The combined-line declarations record directly indexed auxiliary forms of
`lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! The directly indexed obligations below share the extended-line carrier.
The first records the error expression printed in the source as a proposition
that is stated but not asserted; it is a source-gap record, not a theorem.
The second is the conditional auxiliary for a polynomially controlled supplied
point family, carrying the error the first proof route establishes; the third
supplies that family existentially and is the official formalization of what
the source proof establishes at this node. -/

theorem solution
    (deltaQ : ℝ → ℝ) (hdeltaQ : _root_.MIPStarRE.QPBT.IsPolyErr deltaQ) :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ deltaCombine ∧
        ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
          (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S (deltaQ ε)),
          Nonempty (_root_.MIPStarRE.QPBT.ExtendedLinesWitness S points
            (C * (P.m : ℝ) *
              deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  classical
  obtain ⟨deltaP, hdeltaP, hlines⟩ :=
    _root_.MIPStarRE.QPBT.exists_combinedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  obtain ⟨constant, hconstant, hnear⟩ := _root_.MIPStarRE.QPBT.subline_joint_overlap_near_one_at
  obtain ⟨deltaCombine, hdeltaCombine, hscalar⟩ :=
    _root_.MIPStarRE.QPBT.exists_combining_polynomial_bound deltaQ hdeltaQ deltaP hdeltaP constant hconstant.le
  refine ⟨1, by norm_num, deltaCombine, hdeltaCombine, ?_⟩
  intro P ε S points
  obtain ⟨lines⟩ := hlines P ε S points
  obtain ⟨sublines⟩ := _root_.MIPStarRE.QPBT.exists_subLineWitness P
  have hplaced (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.directLinePointDist P.extendedDirectLd)
        (fun sample answer => S.place first
          (((sublines.extendedMeasurement lines first.side sample.1).postprocess
            (fun polynomial => (_root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 polynomial).map
              (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))).effect answer))
        (fun sample answer => S.place second
          (((points.Q second.side (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2))
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2))).postprocess (fun values => some
              ((_root_.MIPStarRE.QPBT.directPointToPauli P sample.2) (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
                (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2) (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2))).effect answer))
        S.psiHat ≤ (P.m : ℝ) * deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)) := by
    refine (le_min ?_ ?_).trans
      (hscalar ε ((P.m * P.d : ℕ) / (P.q : ℝ)) (P.m : ℝ)
        S.eps_nonneg (by positivity) (by exact_mod_cast P.one_le_m))
    · unfold _root_.MIPStarRE.QPBT.consistencyDefect
      calc
        _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directLinePointDist P.extendedDirectLd) (fun _ => 1) :=
          _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun sample =>
            _root_.MIPStarRE.QPBT.consistencyDefect_integrand_le_one S first second hopposite _ _
        _ = 1 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.MIPStarRE.QPBT.directLinePointDist_isProbability _) 1
    · refine (sublines.extended_consistencyDefect_le lines first second hopposite).trans ?_
      exact (le_abs_self _).trans (by
        simpa only [abs_sub_comm] using
          hnear P ε (deltaQ ε) (deltaP ε ((P.m * P.d : ℕ) / (P.q : ℝ)))
            S points lines sublines first second hopposite)
  refine ⟨{
    Qline := sublines.extendedMeasurement lines
    axis_degree := sublines.extendedMeasurement_axis_degree lines
    consistent_alice := ?_
    consistent_bob := ?_ }⟩
  · simp only [one_mul]
    with_unfolding_all exact hplaced .AA' .BA'' trivial
  · simp only [one_mul]
    with_unfolding_all exact hplaced .BB' .AB'' trivial
