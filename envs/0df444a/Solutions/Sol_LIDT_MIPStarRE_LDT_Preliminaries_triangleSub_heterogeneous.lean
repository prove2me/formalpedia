-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:25.657561+00:00
-- url     : https://prove2.me/submissions/4578b8d8-7408-4a1c-bc65-a69c1aa89382

-- Generated proof for MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Triangle Inequalities for State-Dependent Distance: Core

This module contains the main triangle-substitution estimates for approximate
measurements.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT









/-! ### Elementary max bound -/

theorem solution
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιA) (C : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ιB)
    (δ ε : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAC : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) C δ)
    (hAB : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)) ε) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)
      C (δ + Real.sqrt ε) := by
  let AL : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
  let BL : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)
  let CR : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) C
  let matchA : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((AL q).outcome a * (CR q).outcome a)
  let matchB : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((BL q).outcome a * (CR q).outcome a)
  let overlap : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((C q).total))
  let sdd : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.qSDD ψ (AL q) (BL q)
  let gap : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q => matchA q - matchB q
  rcases hAC with ⟨hAC⟩
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed] at hAC
  rcases hAB with ⟨hAB⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    let diagC : _root_.LIDT.MIPStarRE.LDT.Error := ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((CR q).outcome a * (CR q).outcome a)
    have hdiagC_le_one : diagC ≤ 1 := by
      simpa [diagC] using _root_.LIDT.MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ (CR q)
    have haux :
        |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((AL q).outcome a - (BL q).outcome a) *
          (CR q).outcome a)| ≤ Real.sqrt (sdd q) * Real.sqrt diagC := by
      calc
        |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((AL q).outcome a - (BL q).outcome a) *
          (CR q).outcome a)|
          ≤ Real.sqrt
              (∑ a : Outcome,
                _root_.LIDT.MIPStarRE.LDT.ev ψ
                  (((AL q).outcome a - (BL q).outcome a) *
                    ((AL q).outcome a - (BL q).outcome a)ᴴ)) *
              Real.sqrt
                (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((CR q).outcome a)ᴴ * (CR q).outcome a)) := by
                  simpa using
                    _root_.LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt ψ
                      (fun a => (AL q).outcome a - (BL q).outcome a)
                      (fun a => (CR q).outcome a)
        _ = Real.sqrt (sdd q) * Real.sqrt diagC := by
              simp [sdd, _root_.LIDT.MIPStarRE.LDT.qSDD, _root_.LIDT.MIPStarRE.LDT.qSDDCore, diagC, _root_.LIDT.MIPStarRE.LDT.SubMeas.outcome_hermitian]
    have hsqrtC : Real.sqrt diagC ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hdiagC_le_one
    have haux' :
        |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((AL q).outcome a - (BL q).outcome a) *
          (CR q).outcome a)| ≤ Real.sqrt (sdd q) := by
      calc
        |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((AL q).outcome a - (BL q).outcome a) *
          (CR q).outcome a)|
          ≤ Real.sqrt (sdd q) * Real.sqrt diagC := haux
        _ ≤ Real.sqrt (sdd q) * 1 := by
              exact mul_le_mul_of_nonneg_left hsqrtC (Real.sqrt_nonneg _)
        _ = Real.sqrt (sdd q) := by ring
    convert haux' using 1
    dsimp [gap, matchA, matchB]
    refine congrArg abs ?_
    calc
      ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((AL q).outcome a * (CR q).outcome a) -
          ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((BL q).outcome a * (CR q).outcome a)
        = ∑ a : Outcome,
            (_root_.LIDT.MIPStarRE.LDT.ev ψ ((AL q).outcome a * (CR q).outcome a) -
              _root_.LIDT.MIPStarRE.LDT.ev ψ ((BL q).outcome a * (CR q).outcome a)) := by
                rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (((AL q).outcome a - (BL q).outcome a) *
          (CR q).outcome a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(_root_.LIDT.MIPStarRE.LDT.ev_sub ψ ((AL q).outcome a * (CR q).outcome a)
              ((BL q).outcome a * (CR q).outcome a)).symm]
            simp [sub_mul]
  have hgap_avg_abs :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψ (AL q) (BL q))
  have hdefect_pointwise :
      ∀ q, _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (BL q) (CR q) ≤ _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (CR q) + |gap q| := by
    intro q
    have hdefA :
        _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (CR q) = max 0 (overlap q - matchA q) := by
      unfold _root_.LIDT.MIPStarRE.LDT.qConsDefect _root_.LIDT.MIPStarRE.LDT.qMatchMass
      dsimp [overlap, matchA, AL, CR]
      rw [show
        ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) q).total) *
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) C q).total) =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A q).total) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((C q).total) by rfl]
      rw [(A q).total_eq_one]
      simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas,
        _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor]
    have hdefB :
        _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (BL q) (CR q) = max 0 (overlap q - matchB q) := by
      unfold _root_.LIDT.MIPStarRE.LDT.qConsDefect _root_.LIDT.MIPStarRE.LDT.qMatchMass
      dsimp [overlap, matchB, BL, CR]
      rw [show
        ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) q).total) *
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) C q).total) =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((B q).total) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((C q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas,
        _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor]
    calc
      _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (BL q) (CR q)
        = max 0 ((overlap q - matchA q) + gap q) := by
            rw [hdefB]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchA q) + |gap q| := _root_.LIDT.MIPStarRE.LDT.Preliminaries.max_zero_add_le _ _
      _ = _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (CR q) + |gap q| := by
            rw [hdefA]
  constructor
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed]
  unfold _root_.LIDT.MIPStarRE.LDT.consError _root_.LIDT.MIPStarRE.LDT.sddError at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (BL q) (CR q))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (CR q) + |gap q|) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (CR q)) +
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => |gap q|) := by
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
    _ ≤ δ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 sdd) := by
          exact add_le_add hAC hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hAB) δ
