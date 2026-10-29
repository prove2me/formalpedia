-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_one_sub_of_isProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:57:06.435785+00:00
-- url     : https://prove2.me/submissions/52be6af6-cdd4-4608-8696-58b79495a197

-- Generated proof for MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_one_sub_of_isProj.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt
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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/







/-! ## Quadratic forms against projections -/











/-! ## Replacing a factor under the weight of a measurement -/

theorem solution {X α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (B C : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability)
    (hψ : ‖ψ‖ = 1) (hB : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (B x a)) (hC : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (C x a))
    (hAB : ∀ x a, Commute ((A x).effect a) (B x a))
    (hAC : ∀ x a, Commute ((A x).effect a) (C x a)) :
    |avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (C x a * B x a))) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt (1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a))) := by
  have hpt : ∀ x, (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a)) -
      (∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (C x a * B x a))) =
        ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (C x a * (1 - B x a))) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, mul_sub]
  rw [abs_sub_comm, ← _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ hpt]
  have h1B : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (1 - B x a) := fun x a => (hB x a).one_sub
  have hA1B : ∀ x a, Commute ((A x).effect a) (1 - B x a) := fun x a =>
    (Commute.one_right _).sub_right (hAB x a)
  have hcs := _root_.MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A C
    (fun x a => 1 - B x a) ψ hC hAC
  have hsecond : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a)) := by
    have hx : ∀ x, (∑ a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (1 - B x a) ψ) ((A x).effect a)) =
        1 - ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a) := by
      intro x
      rw [← _root_.MIPStarRE.QPBT.sum_stateQForm_effect_eq_one (A x) ψ hψ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [_root_.MIPStarRE.QPBT.stateQForm_applyOperatorToState_eq_of_isProj ψ (h1B x a) (hA1B x a)]
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, mul_sub]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ hx, _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ]
  have hfirst : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a))) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (_root_.MIPStarRE.QPBT.avgOver_sum_stateQForm_mul_le_one μ A C ψ hμ hψ hC hAC)
  rw [hsecond] at hcs
  calc
    _ ≤ _ := hcs
    _ ≤ 1 * Real.sqrt (1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
          ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a))) :=
      mul_le_mul_of_nonneg_right hfirst (Real.sqrt_nonneg _)
    _ = _ := one_mul _
