-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_line_measurement_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:42:25.944556+00:00
-- url     : https://prove2.me/submissions/e9d766a8-ef0a-4bd1-87b4-c9bf9e38181c

-- Generated proof for MIPStarRE.QPBT.combined_line_measurement_consistency.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_CombinedMeasurement
import Definitions.Def_QPBT_QPBT_Combining_Lines_NondegeneratePastingMass
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_ErrorFunctions
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_combined_line_restored_defect_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_le_one
import Theorems.Thm_MIPStarRE_QPBT_exists_conditioned_polynomial_bound

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.Pasting
end MIPStarRE.QPBT.Pasting
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/Sandwich/Pasting/Heterogeneous.lean. -/
/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue
Dengnifer/MIPStarRE-QPBT-bak#495.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus













/-- The fixed heterogeneous pasting error is polynomial in its two inputs. -/
theorem heterogeneous_pasting_error_is_poly_err₂ : _root_.MIPStarRE.QPBT.IsPolyErr₂ _root_.MIPStarRE.QPBT.heterogeneousPastingError := by
  exact ⟨115, 1 / 4, 1 / 8, by norm_num, by norm_num, by norm_num,
    fun η δ hη hδ =>
      ⟨mul_nonneg (by norm_num)
        (add_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg hδ _)), le_rfl⟩⟩



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

/- Source helpers from QPBT/Combining/Lines/Construction.lean. -/
/-!
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section





















/-- A two-variable polynomial error bounds the restored combined-line defect,
including the degenerate-line contribution, with line-marginal coefficient `2080`. -/
theorem exists_combinedLine_restored_defect_le :
    ∃ constant : ℝ, 1 ≤ constant ∧
      ∃ pastingError : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ pastingError ∧
        ∀ (params : _root_.MIPStarRE.QPBT.AdmissibleParams) (error pointError : ℝ)
          (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
          (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError)
          (first second : _root_.MIPStarRE.QPBT.Placement), first.IsOpposite second →
          _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams)
            (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams))
            (fun sample output => setting.place first
              (((points.Q first.side sample.1.2 sample.2.2).postprocess
                (fun pair => (some pair.1, some pair.2))).effect output))
            (fun sample output => setting.place second
              (((setting.combinedLineMeasurement second.side sample.1.1 sample.2.1).postprocess
                (fun polys => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 polys.1,
                  _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 polys.2))).effect output)) setting.psiHat ≤
            _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams *
              pastingError ((params.m * params.d : ℕ) /
                (Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams) : ℝ))
                ((8 * pointError + constant * (error + _root_.MIPStarRE.QPBT.deltaLine error)) /
                  _root_.MIPStarRE.QPBT.nondegenerateLinePastingMass params.toLdParams) +
              1 / (2 * Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams)) := by
  exact ⟨2080, by norm_num, _root_.MIPStarRE.QPBT.heterogeneousPastingError,
    _root_.MIPStarRE.QPBT.heterogeneous_pasting_error_is_poly_err₂, _root_.MIPStarRE.QPBT.combined_line_restored_defect_le_explicit⟩

/-- Consistency is symmetric for measurements on opposite registers. The
operator commutation, rather than symmetry of the state or equality of local
dimensions, justifies exchanging the placements in `lem:qld-xz-lines`. -/
theorem consistencyDefect_opposite_symm {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}
    {Question Outcome : Type*} [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (first second : _root_.MIPStarRE.QPBT.Placement)
    (hopposite : first.IsOpposite second) (distribution : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (left : Question → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (setting.ExpandedLocalSpace first.side))
    (right : Question → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (setting.ExpandedLocalSpace second.side)) :
    _root_.MIPStarRE.QPBT.consistencyDefect distribution
      (fun question answer => setting.place first ((left question).effect answer))
      (fun question answer => setting.place second ((right question).effect answer))
      setting.psiHat =
    _root_.MIPStarRE.QPBT.consistencyDefect distribution
      (fun question answer => setting.place second ((right question).effect answer))
      (fun question answer => setting.place first ((left question).effect answer))
      setting.psiHat := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  congr 1
  funext question
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answer _
  apply Finset.sum_congr rfl
  intro other _
  rw [setting.place_comm first second hopposite]
  simp only [eq_comm]






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
# Construction of consistent combined lines

The heterogeneous pasting theorem bounds the actual X-Z-X measurement.
Polynomial absorption produces a line error for each polynomial point family.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution (deltaQ : ℝ → ℝ)
    (hdeltaQ : _root_.MIPStarRE.QPBT.IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, _root_.MIPStarRE.QPBT.IsPolyErr₂ deltaP ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
        (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S (deltaQ ε))
        (p1 p2 : _root_.MIPStarRE.QPBT.Placement), p1.IsOpposite p2 →
        _root_.MIPStarRE.QPBT.consistencyDefect
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
            (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            (((S.combinedLineMeasurement p1.side sample.1.1 sample.2.1).postprocess
              fun fs => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 fs.1,
                _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
          (fun sample answer => S.place p2
            (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
              (some ab.1, some ab.2)).effect answer))
          S.psiHat ≤ deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) := by
  classical
  obtain ⟨constant, hconstant, pastingError, hpasting, hrestored⟩ :=
    _root_.MIPStarRE.QPBT.exists_combinedLine_restored_defect_le
  obtain ⟨lineError, hlineError, hscalar⟩ :=
    _root_.MIPStarRE.QPBT.exists_conditioned_polynomial_bound deltaQ hdeltaQ constant hconstant pastingError hpasting
  refine ⟨lineError, hlineError, ?_⟩
  intro params error setting points first second hopposite
  have hreverse : second.IsOpposite first := by
    cases first <;> cases second <;> trivial
  rw [_root_.MIPStarRE.QPBT.consistencyDefect_opposite_symm setting first second hopposite]
  have hbound := hrestored params error (deltaQ error) setting points second first hreverse
  have hcard : Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ params.toLdParams) = params.q :=
    @_root_.LIDT.MIPStarRE.LDT.FieldModel.card params.q params.model.toFieldModel
  rw [hcard] at hbound
  have hq : (0 : ℝ) < params.q := by
    rw [← hcard]
    exact_mod_cast Fintype.card_pos (α := _root_.MIPStarRE.QPBT.ScalarQ params.toLdParams)
  have hmd : (1 : ℝ) ≤ (params.m * params.d : ℕ) := by
    exact_mod_cast (show 1 ≤ params.m * params.d by
      simpa using Nat.mul_le_mul params.one_le_m params.hd)
  have hdiscard : 1 / (2 * (params.q : ℝ)) ≤
      (params.m * params.d : ℕ) / (params.q : ℝ) := by
    calc
      _ ≤ 1 / (params.q : ℝ) := one_div_le_one_div_of_le hq (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hmd hq.le
  have hunit : _root_.MIPStarRE.QPBT.consistencyDefect
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams) (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams))
      (fun sample answer => setting.place second
        (((points.Q second.side sample.1.2 sample.2.2).postprocess
          (fun pair => (some pair.1, some pair.2))).effect answer))
      (fun sample answer => setting.place first
        (((setting.combinedLineMeasurement first.side sample.1.1 sample.2.1).postprocess
          (fun polys => (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 polys.1,
            _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 polys.2))).effect answer)) setting.psiHat ≤ 1 := by
    unfold _root_.MIPStarRE.QPBT.consistencyDefect
    calc
      _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist params.toLdParams)) (fun _ => 1) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun sample =>
          _root_.MIPStarRE.QPBT.consistencyDefect_integrand_le_one setting second first hreverse _ _
      _ = 1 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _
        (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _ (_root_.MIPStarRE.QPBT.linePointDist_isProbability params.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist_isProbability params.toLdParams)) 1
  exact (le_min hunit (hbound.trans (add_le_add le_rfl hdiscard))).trans
    (hscalar error _ _ setting.eps_nonneg (by positivity)
      (_root_.MIPStarRE.QPBT.nondegenerateLinePastingMass_bounds params.toLdParams).1
      (_root_.MIPStarRE.QPBT.nondegenerateLinePastingMass_bounds params.toLdParams).2)
