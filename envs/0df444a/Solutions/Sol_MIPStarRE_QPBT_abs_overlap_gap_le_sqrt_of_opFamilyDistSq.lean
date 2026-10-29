-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_of_opFamilyDistSq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:44:57.189474+00:00
-- url     : https://prove2.me/submissions/dcf16320-babb-42ad-9670-4abf37da5b9e

-- Generated proof for MIPStarRE.QPBT.abs_overlap_gap_le_sqrt_of_opFamilyDistSq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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









































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

















































end MIPStarRE.QPBT.DistanceCalculus

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

theorem solution {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (B C : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ) (hBC : _root_.MIPStarRE.QPBT.opFamilyDistSq μ B C ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a)) -
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a))| ≤
      Real.sqrt ζ := by
  classical
  have hnorm_sq : ∀ M : _root_.LIDT.MIPStarRE.Quantum.Op ι,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Mᴴ * M) := by
    intro M
    rw [@norm_sq_eq_re_inner ℂ]
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
    rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
    change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
      (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
        (Matrix.toEuclideanLin M ψ))).re
    rw [LinearMap.adjoint_inner_right]
  have hmul : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op ι, Mᴴ = M →
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * N) =
        (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState M ψ)
          (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ)).re := by
    intro M N hM
    have hadjoint : (Matrix.toEuclideanLin M).adjoint =
        Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
    calc
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * N) =
          (inner ℂ ψ
            (_root_.MIPStarRE.QPBT.applyOperatorToState M (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ))).re := by
        rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
      _ = (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint
            (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ))).re := by
        rw [hadjoint]
        rfl
      _ = _ := by
        rw [LinearMap.adjoint_inner_right]
        rfl
  have hleft : ∀ x : X,
      (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤ 1 := by
    intro x
    have htotal : (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a)) = 1 := by
      calc
        (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a)) =
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ a : α, (A x).effect a) := by
          simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
        _ = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 1 := by rw [(A x).sum_eq_one]
        _ = 1 := by rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm]; simp [_root_.MIPStarRE.QPBT.applyOperatorToState, hψ]
    calc
      (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState ((A x).effect a) ψ‖ ^ 2) ≤
          ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a) := by
        refine Finset.sum_le_sum ?_
        intro a _
        rw [hnorm_sq, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
        exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono (_root_.LIDT.MIPStarRE.Quantum.sq_le_self ((A x).pos a)
          (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one (A x) a)) ψ
      _ = 1 := htotal
  have hgnonneg : ∀ x : X,
      0 ≤ ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2 :=
    fun x => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint : ∀ x : X,
      |∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x a - C x a))| ≤
        Real.sqrt (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := by
    intro x
    let u : α → EuclideanSpace ℂ ι := fun a =>
      _root_.MIPStarRE.QPBT.applyOperatorToState ((A x).effect a) ψ
    let v : α → EuclideanSpace ℂ ι := fun a =>
      _root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ
    have hrw : (∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x a - C x a))) =
        ∑ a : α, (inner ℂ (u a) (v a)).re := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact hmul _ _ (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (A x) a)
    have hone : Real.sqrt (∑ a : α, ‖u a‖ ^ 2) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (hleft x)
    calc
      |∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x a - C x a))| =
          |∑ a : α, (inner ℂ (u a) (v a)).re| := by rw [hrw]
      _ ≤ ∑ a : α, |(inner ℂ (u a) (v a)).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : α, ‖u a‖ * ‖v a‖ := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (u a) (v a))
      _ ≤ Real.sqrt (∑ a : α, ‖u a‖ ^ 2) * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset α) (fun a => ‖u a‖) (fun a => ‖v a‖)
      _ ≤ 1 * Real.sqrt (∑ a : α, ‖v a‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ a : α,
            ‖_root_.MIPStarRE.QPBT.applyOperatorToState (B x a - C x a) ψ‖ ^ 2) := one_mul _
  have hdiff :
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * B x a)) -
          _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * C x a)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x a - C x a))) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub]
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ ?_
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState, mul_sub]
  rw [hdiff]
  refine le_trans
    (_root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise μ _ _
      hpoint hgnonneg (by rw [hμ.weight_sum_eq_one])) ?_
  exact Real.sqrt_le_sqrt hBC
