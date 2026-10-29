-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj_prime
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:01.860051+00:00
-- url     : https://prove2.me/submissions/c70e5aea-1db7-45a5-91ed-eabe601854c0

-- Generated proof for MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj'.
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
import Theorems.Thm_MIPStarRE_QPBT_abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
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
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (W R : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) (hR : ∀ x a, _root_.LIDT.MIPStarRE.Quantum.IsProj (R x a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a)) :
    |avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (W x a * R x a)))| ≤
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x =>
        ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (W x a)ᴴ ψ‖ ^ 2)) := by
  have hrw : ∀ x a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (W x a * R x a)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (R x a * (W x a)ᴴ)) := by
    intro x a
    have hAWH : Commute ((A x).effect a) (W x a)ᴴ := by
      have h := congrArg Matrix.conjTranspose (hAW x a).eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian] at h
      exact h.symm
    rw [← _root_.MIPStarRE.QPBT.stateQForm_conjTranspose ψ ((A x).effect a * (W x a * R x a)),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian, (hR x a).isSelfAdjoint.isHermitian.eq]
    congr 1
    exact ((hAR x a).mul_right hAWH).eq.symm
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ => hrw x a]
  exact _root_.MIPStarRE.QPBT.abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj μ A R
    (fun x a => (W x a)ᴴ) ψ hμ hψ hR hAR
