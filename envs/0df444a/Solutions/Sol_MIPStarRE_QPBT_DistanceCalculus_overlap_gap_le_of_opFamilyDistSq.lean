-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.overlap_gap_le_of_opFamilyDistSq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.989983+00:00
-- url     : https://prove2.me/submissions/c07c6e43-76a4-43e1-8cd7-6dcde4b59c68

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.overlap_gap_le_of_opFamilyDistSq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_toQuantumState_isNormalized

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
private theorem norm_applyOperatorToState_sq_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]















































































/-- For a unit vector, `stateQForm` agrees with the LDT pure-state expectation.
This is `pureState_stateQForm_eq_ev` read along `pureStateOfUnitVector`. -/
private theorem stateQForm_eq_ev {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ T = _root_.LIDT.MIPStarRE.LDT.ev (pureStateOfUnitVector ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) T :=
  _root_.MIPStarRE.QPBT.DistanceCalculus.pureState_stateQForm_eq_ev (pureStateOfUnitVector ψ hψ) T

/-- Pure-state evaluation of `Tᴴ T` is the squared norm of `T ψ`. -/
private theorem ev_adjoint_mul_self_eq_norm_sq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (T : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev (pureStateOfUnitVector ψ hψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) (Tᴴ * T) =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState T ψ‖ ^ 2 := by
  rw [← stateQForm_eq_ev]
  exact (norm_applyOperatorToState_sq_eq T ψ).symm







end MIPStarRE.QPBT.DistanceCalculus

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {X α ι : Type*}
    [Fintype α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A B D : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (ζ : ℝ)
    (hBD : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ζ) :
    |avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) -
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (D x).effect a))| ≤
        Real.sqrt ζ := by
  classical
  let ψp : _root_.LIDT.MIPStarRE.LDT.PureState ι := pureStateOfUnitVector ψ hψ
  let H : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace :=
    { carrier := ι
      instFintype := inferInstance
      instDecidableEq := inferInstance
      instNonempty := inferInstance }
  let As : X → _root_.LIDT.MIPStarRE.LDT.SubMeas α ι := fun x =>
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := H) (A x)).toSubMeas
  let Bs : X → _root_.LIDT.MIPStarRE.LDT.SubMeas α ι := fun x =>
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := H) (B x)).toSubMeas
  let Ds : X → _root_.LIDT.MIPStarRE.LDT.SubMeas α ι := fun x =>
    (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := H) (D x)).toSubMeas
  have hmass : ∑ x ∈ μ.support, μ.weight x ≤ 1 := by
    rw [hμ.weight_sum_eq_one]
  have hsdd : _root_.LIDT.MIPStarRE.LDT.SDDRel (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) μ Bs Ds ζ := by
    constructor
    unfold _root_.LIDT.MIPStarRE.LDT.sddError _root_.LIDT.MIPStarRE.LDT.qSDD _root_.LIDT.MIPStarRE.LDT.qSDDCore
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
          (((Bs x).outcome a - (Ds x).outcome a)ᴴ *
            ((Bs x).outcome a - (Ds x).outcome a))) =
          _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
            (fun x a => (D x).effect a) ψ := by
        unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro x
        apply Finset.sum_congr rfl
        intro a _
        simpa [ψp, Bs, Ds, H] using
          ev_adjoint_mul_self_eq_norm_sq ψ hψ ((B x).effect a - (D x).effect a)
      _ ≤ ζ := hBD
  have hgap := _root_.LIDT.MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta
    (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ψp.toQuantumState_isNormalized μ hmass Bs Ds As ζ hsdd
  have hBA : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((A x).effect a * (B x).effect a)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((B x).effect a * (A x).effect a)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact _root_.LIDT.MIPStarRE.LDT.ev_mul_comm_of_psd _ _ _ ((A x).pos a) ((B x).pos a)
  have hDA : _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((A x).effect a * (D x).effect a)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((D x).effect a * (A x).effect a)) := by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact _root_.LIDT.MIPStarRE.LDT.ev_mul_comm_of_psd _ _ _ ((A x).pos a) ((D x).pos a)
  rw [show _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((A x).effect a * (B x).effect a)) by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact stateQForm_eq_ev ψ hψ _]
  rw [show _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (D x).effect a)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.LIDT.MIPStarRE.LDT.ev (ψp : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) ((A x).effect a * (D x).effect a)) by
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro x
    apply Finset.sum_congr rfl
    intro a _
    exact stateQForm_eq_ev ψ hψ _]
  rw [hBA, hDA]
  simpa only [ψp, As, Bs, Ds, H,
    MatrixMeasurement.toMeasurement_outcome] using hgap
