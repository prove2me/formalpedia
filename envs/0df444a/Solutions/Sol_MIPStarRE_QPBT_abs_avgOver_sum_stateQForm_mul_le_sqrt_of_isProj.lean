-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:57:06.259857+00:00
-- url     : https://prove2.me/submissions/1e750123-1c30-4cc8-89bc-dc658a365f7f

-- Generated proof for MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj.
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
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
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





/-- The quadratic form of an operator bounded by the identity is bounded by
the squared norm of the vector. -/
theorem stateQForm_le_norm_sq_of_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) {A : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hA : A ≤ 1) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm v A ≤ ‖v‖ ^ 2 := by
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hA v





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

theorem solution {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (R W : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a)) :
    |avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (R x a * W x a)))| ≤
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (W x a) ψ‖ ^ 2)) := by
  have hcs := _root_.MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A R W ψ hR hAR
  have hfirst : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * R x a))) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt
      (_root_.MIPStarRE.QPBT.avgOver_sum_stateQForm_mul_le_one μ A R ψ hμ hψ hR hAR)
  have hsecond : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.applyOperatorToState (W x a) ψ) ((A x).effect a)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (W x a) ψ‖ ^ 2) :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_mono μ _ _ fun x => Finset.sum_le_sum fun a _ =>
      _root_.MIPStarRE.QPBT.stateQForm_le_norm_sq_of_le_one _ (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one (A x) a)
  calc
    _ ≤ _ := hcs
    _ ≤ 1 * Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
          ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (W x a) ψ‖ ^ 2)) :=
      mul_le_mul hfirst (Real.sqrt_le_sqrt hsecond) (Real.sqrt_nonneg _)
        zero_le_one
    _ = _ := one_mul _
