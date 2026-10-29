-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_globalPairWitness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:50:43.551988+00:00
-- url     : https://prove2.me/submissions/0edc13ea-7e8f-4193-9bd7-71680629c134

-- Generated proof for MIPStarRE.QPBT.exists_globalPairWitness.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_PassingError
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_pair_witness_of_points_lines_explicit
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_le_one
import Theorems.Thm_MIPStarRE_QPBT_exists_actual_rounded_global_pair_error_bound
import Theorems.Thm_MIPStarRE_QPBT_exists_combined_points_witness_explicit
import Theorems.Thm_MIPStarRE_QPBT_exists_extendedLinesWitness_established_ofPointsWitness

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean. -/
/-!
# Point consistency of the completed polynomial-pair measurements

The polynomial-pair completion is applied to the actual rounded outcomes. Its missing
mass and retained point mismatch are kept separate until the final bound.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1375-1404`,
`eq:qld-sgg-completeness` and `eq:qld-sgg-mhat-sandwich`;
blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.ExtendedLineGame

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus PolynomialImageBounds

noncomputable section






















/-- There are universal low-degree constants for which supplied point and
extended-line witnesses determine complete projective polynomial-pair
measurements satisfying all four point-consistency bounds. -/
theorem exists_pairWitness_of_points_lines :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δL : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (_lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness S points δL),
      let delta := _root_.MIPStarRE.QPBT.deltaLd a b
        (_root_.MIPStarRE.QPBT.directPassingErrorEnvelope (δQ + δL) ((P.m * P.d : ℝ) / P.q))
        P.q (2 * P.m + 2) P.d 1
      let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta)
      Nonempty (_root_.MIPStarRE.QPBT.GlobalPairWitness S (8 * (4 * eta + 8 * δQ) +
        (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q))) := by
  refine ⟨_root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant, _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower, ?_, ?_, ?_,
    _root_.MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_explicit⟩
  · unfold _root_.MIPStarRE.QPBT.pauliBaselineLowDegreeConstant
    norm_num
  · unfold _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
    norm_num
  · unfold _root_.MIPStarRE.QPBT.pauliBaselineLowDegreePower
    norm_num

end

end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/Points.lean. -/
/-!
# Combining the point measurements

This module constructs the projective joint X/Z point measurements and defines
their scalar linear coarse-graining. The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







/-- The fixed polynomial error `pauliBaselinePointConstant * ε^(1/8)` produces a
combined-point witness for every projective Pauli-test setting. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, _root_.MIPStarRE.QPBT.IsPolyErr deltaQ ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
        Nonempty (_root_.MIPStarRE.QPBT.CombinedPointsWitness S (deltaQ ε)) := by
  have hQ : (1 : ℝ) ≤ _root_.MIPStarRE.QPBT.pauliBaselinePointConstant := by
    simp only [_root_.MIPStarRE.QPBT.pauliBaselinePointConstant, _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant,
      _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  refine ⟨fun ε => _root_.MIPStarRE.QPBT.pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ),
    ⟨_root_.MIPStarRE.QPBT.pauliBaselinePointConstant, 1 / 8, hQ, by norm_num, fun ε hε =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hε _), le_rfl⟩⟩,
    _root_.MIPStarRE.QPBT.exists_combined_points_witness_explicit⟩







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

/- Source helpers from QPBT/Combining/Apply.lean. -/
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

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! The directly indexed obligations below share the extended-line carrier.
The first records the error expression printed in the source as a proposition
that is stated but not asserted; it is a source-gap record, not a theorem.
The second is the conditional auxiliary for a polynomially controlled supplied
point family, carrying the error the first proof route establishes; the third
supplies that family existentially and is the official formalization of what
the source proof establishes at this node. -/







/-- Directly indexed construction for the auxiliary estimate
`C * m * poly(epsilon, md / q)`. This has the same directly indexed estimate as
`exists_extendedLinesWitness_established_ofPointsWitness`, with the point witness
existentially supplied rather than assumed.

Its question carrier and line-point law are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; its `Option`-completed answer
alphabet is documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Transport to `lem:qld-4-13` must convert this completed comparison to the source's
sum over field answers, including degenerate zero-direction singleton lines. The
printed error form of `lem:qld-4-13` is not claimed here and remains an open
source gap, tracked by issue Dengnifer/MIPStarRE-QPBT-bak#598.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue
Dengnifer/MIPStarRE-QPBT-bak#196.
Here `poly(epsilon, md / q)` is read in that sense.

The proof constructs the polynomially controlled point family of `lem:qld-4-10`
and applies the conditional companion above to that same family. -/
theorem exists_extendedLinesWitness_established :
    ∃ deltaQ : ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr deltaQ ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ deltaCombine : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ deltaCombine ∧
          ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
            ∃ points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S (deltaQ ε),
              Nonempty (_root_.MIPStarRE.QPBT.ExtendedLinesWitness S points
                (C * (P.m : ℝ) *
                  deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  classical
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := _root_.MIPStarRE.QPBT.exists_combinedPointsWitness
  obtain ⟨C, hC, deltaCombine, hdeltaCombine, hlines⟩ :=
    _root_.MIPStarRE.QPBT.exists_extendedLinesWitness_established_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, C, hC, deltaCombine, hdeltaCombine, ?_⟩
  intro P ε S
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩





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

theorem solution :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
        Nonempty (_root_.MIPStarRE.QPBT.GlobalPairWitness S (_root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q)) := by
  obtain ⟨pointError, hpoint, C, hC, lineError, hline, hlines⟩ :=
    _root_.MIPStarRE.QPBT.exists_extendedLinesWitness_established
  obtain ⟨a, b, ha, hb, hb1, hpairs⟩ :=
    _root_.MIPStarRE.QPBT.ExtendedLineGame.exists_pairWitness_of_points_lines
  obtain ⟨A, B, hA, hB, hB1, hscalar⟩ :=
    _root_.MIPStarRE.QPBT.exists_actual_rounded_global_pair_error_bound pointError hpoint lineError hline
      C a b hC.le ha hb hb1
  refine ⟨A, B, hA, hB, hB1, ?_⟩
  intro P ε S
  obtain ⟨points, ⟨lines⟩⟩ := hlines P ε S
  obtain ⟨pair⟩ := hpairs P ε (pointError ε)
    (C * (P.m : ℝ) * lineError ε ((P.m * P.d : ℕ) / (P.q : ℝ))) S points lines
  have hbound := hscalar P ε S.eps_nonneg
  simp only [Nat.cast_mul] at hbound
  refine ⟨{ pair with point_consistent_alice := ?_, point_consistent_bob := ?_ }⟩
  · intro W
    refine (le_min (show _ ≤ (1 : ℝ) from ?_) (pair.point_consistent_alice W)).trans ?_
    · unfold _root_.MIPStarRE.QPBT.consistencyDefect
      calc
        _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun _ => 1) :=
          _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun u => _root_.MIPStarRE.QPBT.consistencyDefect_integrand_le_one
            S .AA' .BA'' (by trivial) _ _
        _ = 1 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) 1
    · with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound
  · intro W
    refine (le_min (show _ ≤ (1 : ℝ) from ?_) (pair.point_consistent_bob W)).trans ?_
    · unfold _root_.MIPStarRE.QPBT.consistencyDefect
      calc
        _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun _ => 1) :=
          _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun u => _root_.MIPStarRE.QPBT.consistencyDefect_integrand_le_one
            S .BB' .AB'' (by trivial) _ _
        _ = 1 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) 1
    · with_unfolding_all simpa only [Nat.cast_mul, Real.rpow_eq_pow] using hbound
