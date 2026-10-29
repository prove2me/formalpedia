-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.diagonal_postprocess_stateQForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.83099+00:00
-- url     : https://prove2.me/submissions/9d3846ba-e1e8-4281-badd-e8c0247310e1

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.diagonal_postprocess_stateQForm_ge.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective









/-- Evaluation in the rank-one vector state is the corresponding quadratic form. -/
private theorem vectorQuantumState_ev_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (T : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev (vectorQuantumState ψ) T = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ T := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change (_root_.LIDT.MIPStarRE.Quantum.normalizedTrace (_root_.LIDT.MIPStarRE.LDT.pureDensity ψ.ofLp * T)).re =
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ T
  rw [_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_mul_comm]
  unfold _root_.LIDT.MIPStarRE.LDT.pureDensity _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec]
  change (((Fintype.card ι : ℂ) *
      ((T *ᵥ ψ.ofLp) ⬝ᵥ star ψ.ofLp)) /
      (Fintype.card ι : ℂ)).re = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ T
  rw [mul_div_cancel_left₀ _ hcard]
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]



























end MIPStarRE.QPBT.DistanceCalculus

/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (f : α → β) :
    (∑ b : β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) ≥
      ∑ a : α, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a)) := by
  classical
  cases isEmpty_or_nonempty (ιA × ιB) with
  | inl hι =>
      letI := hι
      have hψ : ψ = 0 := Subsingleton.elim _ _
      subst ψ
      simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  | inr hι =>
      letI := hι
      letI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
      letI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
      let HA : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace :=
        { carrier := ιA
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let HB : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace :=
        { carrier := ιB
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let As : _root_.LIDT.MIPStarRE.LDT.SubMeas α ιA :=
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HA) A).toSubMeas
      let Bs : _root_.LIDT.MIPStarRE.LDT.SubMeas α ιB :=
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement (H := HB) B).toSubMeas
      have hAoutcome (a : α) : As.outcome a = A.effect a := by
        simp [As, HA]
      have hBoutcome (a : α) : Bs.outcome a = B.effect a := by
        simp [Bs, HB]
      have hApost (b : β) :
          (_root_.LIDT.MIPStarRE.LDT.postprocess As f).outcome b =
            (A.postprocess f).effect b := by
        rw [_root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome,
          _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        apply Finset.sum_congr rfl
        intro a _
        exact hAoutcome a
      have hBpost (b : β) :
          (_root_.LIDT.MIPStarRE.LDT.postprocess Bs f).outcome b =
            (B.postprocess f).effect b := by
        rw [_root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome,
          _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        apply Finset.sum_congr rfl
        intro a _
        exact hBoutcome a
      have h := _root_.LIDT.MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        (vectorQuantumState ψ) As Bs f
      unfold _root_.LIDT.MIPStarRE.LDT.qMatchMass at h
      simp only [leftPlacedSubMeas_outcome, rightPlacedSubMeas_outcome] at h
      simpa only [hAoutcome, hBoutcome, hApost, hBpost,
        _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
        vectorQuantumState_ev_eq_stateQForm, _root_.MIPStarRE.QPBT.heteroKron] using h
