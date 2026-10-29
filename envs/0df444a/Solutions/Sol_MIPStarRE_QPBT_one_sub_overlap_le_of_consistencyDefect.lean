-- Prove2me | solution 1 for MIPStarRE.QPBT.one_sub_overlap_le_of_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:37.31798+00:00
-- url     : https://prove2.me/submissions/ec759ef7-36bc-45f6-9908-a90e9eb67a79

-- Generated proof for MIPStarRE.QPBT.one_sub_overlap_le_of_consistencyDefect.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj_prime
import Theorems.Thm_MIPStarRE_QPBT_abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt
import Theorems.Thm_MIPStarRE_QPBT_abs_overlap_gap_le_sqrt_of_opFamilyDistSq
import Theorems.Thm_MIPStarRE_QPBT_avgOver_sum_stateQForm_mul_le_one

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





































/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖ψ‖ ^ 2 := by
  have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hone]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)

/-- The quadratic form of `Wᴴ M W` in `ψ` is the quadratic form of `M` in
`W ψ`.  This is the conjugation identity behind the placed-sandwich
rewritings: conjugating transfers the outer operator to the state vector.
It is formalization-only auxiliary content, shared by the overlap-gap estimate
and the sandwich self-consistency argument. -/
theorem stateQForm_conjTranspose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (W M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Wᴴ * M * W) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState W ψ) M := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
  congr 1
  change inner ℂ ψ (Matrix.toEuclideanLin Wᴴ _) =
    inner ℂ (Matrix.toEuclideanLin W ψ) _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]



















































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/OverlapGap.lean. -/
/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/







/-! ## Quadratic forms against projections -/

/-- The real quadratic form is invariant under the conjugate transpose. -/
theorem stateQForm_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ Mᴴ = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  change (inner ℂ ψ (Matrix.toEuclideanLin Mᴴ ψ)).re =
    (inner ℂ ψ (Matrix.toEuclideanLin M ψ)).re
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
    ← inner_conj_symm, Complex.conj_re]

/-- For a projection `B` commuting with `A`, the quadratic form of `A` in
`B ψ` is the quadratic form of `A B` in `ψ`. -/
theorem stateQForm_applyOperatorToState_eq_of_isProj {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) {A B : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hB : _root_.LIDT.MIPStarRE.Quantum.IsProj B)
    (hAB : Commute A B) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState B ψ) A = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A * B) := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_conjTranspose_mul_mul, hB.isSelfAdjoint.isHermitian.eq,
    ← hAB.eq, mul_assoc, hB.isIdempotentElem.eq]



/-- The effects of a complete measurement have total quadratic form one on a
unit vector. -/
theorem sum_stateQForm_effect_eq_one {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a)) = 1 := by
  calc
    (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (A.effect a)) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ a : α, A.effect a) := by
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 1 := by rw [A.sum_eq_one]
    _ = 1 := by rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one, hψ, one_pow]



/-! ## Replacing a factor under the weight of a measurement -/











end MIPStarRE.QPBT

/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Completed point pairs -/









open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}












/-! ## The abstract one-point deficit -/

theorem solution {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A Q : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (R W : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hQ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q x)) (hR : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (R x a))
    (hAQ : ∀ x a, Commute ((A x).effect a) ((Q x).effect a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a))
    (hWR : ∀ x a, W x a * R x a = W x a)
    (hnonneg : ∀ x a, 0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (Q x).effect a))
    (η ζ : ℝ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (Q x).effect a) ψ ≤ η)
    (hdist : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (Q x).effect a)
      (fun x a => (W x a)ᴴ) ψ ≤ ζ) :
    1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  set ovQ := _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
    ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (Q x).effect a)) with hovQ
  have h1 : 1 - ovQ ≤ η := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A Q ψ hμ hψ]
    exact hcons
  have hovQ_nonneg : 0 ≤ ovQ :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => hnonneg x a
  have hovQ_le : ovQ ≤ 1 :=
    _root_.MIPStarRE.QPBT.avgOver_sum_stateQForm_mul_le_one μ A (fun x a => (Q x).effect a) ψ hμ hψ
      (fun x a => hQ x a) hAQ
  have h1' : 1 - ovQ ≤ Real.sqrt η := by
    have h0 : 0 ≤ 1 - ovQ := by linarith
    calc 1 - ovQ = Real.sqrt ((1 - ovQ) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt (by nlinarith)
  -- comparing `Q` with `W` under the weight `A`
  have hWconj : ∀ x a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * W x a) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (W x a)ᴴ) := by
    intro x a
    rw [← _root_.MIPStarRE.QPBT.stateQForm_conjTranspose ψ ((A x).effect a * W x a),
      Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    congr 1
    have h := congrArg Matrix.conjTranspose (hAW x a).eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian] at h
    exact h
  have h2 : |ovQ - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * W x a))| ≤ Real.sqrt ζ := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hWconj x a]
    exact _root_.MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_of_opFamilyDistSq μ A
      (fun x a => (Q x).effect a) (fun x a => (W x a)ᴴ) ψ hμ hψ ζ hdist
  -- replacing `Q R` by `W R = W`
  have h4 : |avgOver μ (fun x =>
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * W x a))| ≤
      Real.sqrt ζ := by
    have hpt : ∀ x,
        (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
          (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * W x a)) =
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (((Q x).effect a - W x a) * R x a)) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sub_mul, hWR]
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, mul_sub]
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ hpt]
    have hcs := _root_.MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj_prime μ A
      (fun x a => (Q x).effect a - W x a) R ψ hμ hψ hR hAR
      (fun x a => (hAQ x a).sub_right (hAW x a))
    refine hcs.trans (Real.sqrt_le_sqrt ?_)
    have hdist' : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((Q x).effect a - (W x a)ᴴ) ψ‖ ^ 2) ≤ ζ :=
      hdist
    refine le_of_eq_of_le ?_ hdist'
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_sub, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
  -- inserting `Q` before `R`
  have h5 : |avgOver μ (fun x =>
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * R x a))| ≤
      Real.sqrt η := by
    have hpt : ∀ x,
        (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * R x a)) -
          (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) =
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * ((1 - (Q x).effect a) * R x a)) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, sub_mul, mul_sub]
    rw [abs_sub_comm, ← _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ hpt]
    have hcs := _root_.MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A
      (fun x a => 1 - (Q x).effect a) R ψ (fun x a => (hQ x a).one_sub)
      (fun x a => (Commute.one_right _).sub_right (hAQ x a))
    have hfirst : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) = 1 - ovQ := by
      have hx : ∀ x,
          (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) =
            1 - ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (Q x).effect a) := by
        intro x
        rw [← _root_.MIPStarRE.QPBT.sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, mul_sub]
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ hx, _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ]
    have hsecond : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (R x a) ψ) ((A x).effect a)) ≤ 1 := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ =>
        _root_.MIPStarRE.QPBT.stateQForm_applyOperatorToState_eq_of_isProj ψ (hR x a) (hAR x a)]
      exact _root_.MIPStarRE.QPBT.avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR
    rw [hfirst] at hcs
    calc
      _ ≤ _ := hcs
      _ ≤ Real.sqrt (1 - ovQ) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hsecond
      _ = Real.sqrt (1 - ovQ) := mul_one _
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt h1
  have h2' := abs_le.mp h2
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  linarith [h2'.1, h4'.1, h5'.1, h2'.2, h4'.2, h5'.2]
