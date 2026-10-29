-- Prove2me | solution 1 for MIPStarRE.QPBT.subline_z_term_near_one_at_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:32:47.6033+00:00
-- url     : https://prove2.me/submissions/e3fe006f-fdf0-4b02-828b-fac689413006

-- Generated proof for MIPStarRE.QPBT.subline_z_term_near_one_at_explicit.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_SubLineZDeficit
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_avgOver_zPointOverlap_le_one_at
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_one_sub_avgOver_zPointOverlap_le_at
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_nonneg
import Theorems.Thm_MIPStarRE_QPBT_sqrt_deficit_bound_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/ErrorBounds.lean. -/
/-! # Scalar error bounds for combining polynomial measurements

This module proves the formalization-only scalar estimates used by the combining
argument: nonnegativity of the real fourth root, the quarter-power form of a
square root of two deficit terms, polynomial bounds after conditioning,
composition with the dimension factor retained, and absorption into the global
polynomial-pair error scale. The estimates quantify over error functions and
numerical parameters; they do not construct measurements, and none of them is
specific to Claims 17-1 through 17-3.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The real fourth root is nonnegative on all of `ℝ`. For `x < 0` the real power
`x ^ (1/4)` is defined as `|x| ^ (1/4) * cos (π/4)`, which is positive, and for
`0 ≤ x` it is the usual fourth root. The estimates of `lem:qld-4-13` are stated
with quarter powers of error quantities whose nonnegativity is not always
available at the point of use, so the bound is recorded without a sign
hypothesis. -/
theorem rpow_quarter_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / 4 : ℝ) := by
  change 0 ≤ x ^ (1 / 4 : ℝ)
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx,
      show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  · exact Real.rpow_nonneg hx _















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































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)





























end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/





/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem pointMeasExpOption_effect_evalOpt (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d)) :
    (S.pointMeasExpOption side W u).effect (_root_.MIPStarRE.QPBT.evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointEffectAtLineAnswer
  cases _root_.MIPStarRE.QPBT.evalOpt line u f with
  | none => exact S.pointMeasExpOption_effect_none side W u
  | some a => exact S.pointMeasExpOption_effect_some side W u a





/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/SubLineZDeficit.lean. -/
/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Regrouping the line answers by their evaluations -/









/-! ## The two one-point overlaps -/

section Overlaps

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}









/-- The `Z`-point overlap is nonnegative. -/
theorem zPointOverlap_nonneg_at (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second)
    (w : (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) ×
      (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) :
    0 ≤ _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second w :=
  Finset.sum_nonneg fun fX _ => Finset.sum_nonneg fun fZ _ =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg _ (S.place_mul_place_nonneg first second hopposite
      ((lines.T first.side w.1.1 w.1.2).pos (fX, fZ))
      ((S.pointMeasExpOption second.side .Z w.2).pos (_root_.MIPStarRE.QPBT.evalOpt w.1.2 w.2 fZ)))












end Overlaps

end

end MIPStarRE.QPBT

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



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ δP : ℝ)
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP) (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    |avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) (fun t =>
          let u := _root_.MIPStarRE.QPBT.directPointToPauli P
            (sample.1.base + t • sample.1.direction)
          let z := _root_.MIPStarRE.QPBT.projZ u
          ∑ fX, ∑ fZ,
            (inner ℂ S.psiHat ((EuclideanSpace.equiv
              (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                ((S.place first
                    ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                  S.place second
                    (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                      S.psiHat))).re)) - 1| ≤
      2 * Real.sqrt (P.m : ℝ) *
        (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
          Real.rpow ε (1 / 4 : ℝ)) := by
  classical
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold _root_.MIPStarRE.QPBT.consistencyDefect
    exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun s =>
      _root_.MIPStarRE.QPBT.consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hLHS : _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := _root_.MIPStarRE.QPBT.directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let z := _root_.MIPStarRE.QPBT.projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (_root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place first
                  ((lines.T first.side sample.2.1 sample.2.2).effect (fX, fZ)) *
                S.place second
                  (S.expPointEffectAtLineAnswer second.side .Z sample.2.2 z fZ)).mulVec
                    S.psiHat))).re)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
          (fun t => _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun sample => _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun t => ?_
    simp only [_root_.MIPStarRE.QPBT.zPointOverlapAt, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
    rfl
  rw [hLHS]
  set L := _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
      (fun t => _root_.MIPStarRE.QPBT.zPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
        (sample.1.base + t • sample.1.direction))))) with hL
  have hdef := sublines.one_sub_avgOver_zPointOverlap_le_at lines first second hopposite
  have hle := sublines.avgOver_zPointOverlap_le_one_at lines first second hopposite
  have hnonneg : 0 ≤ L :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun sample => _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun t =>
      _root_.MIPStarRE.QPBT.zPointOverlap_nonneg_at lines first second hopposite _
  rw [← hL] at hdef hle
  have h0 : 0 ≤ 1 - L := by linarith
  have hsq : (1 - L) ^ 2 ≤ 1 - L := by nlinarith
  calc
    |L - 1| = 1 - L := by rw [abs_sub_comm, abs_of_nonneg h0]
    _ = Real.sqrt ((1 - L) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) +
          2 * Real.sqrt (4 * δQ)) := Real.sqrt_le_sqrt (hsq.trans hdef)
    _ ≤ 2 * Real.sqrt (P.m : ℝ) *
          (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) :=
      _root_.MIPStarRE.QPBT.sqrt_deficit_bound_le _ _ _ hm hδP hδQ
    _ ≤ _ := by
      have hε := _root_.MIPStarRE.QPBT.rpow_quarter_nonneg ε
      have hsm : 0 ≤ 2 * Real.sqrt (P.m : ℝ) :=
        mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
      nlinarith [mul_nonneg hsm hε]
