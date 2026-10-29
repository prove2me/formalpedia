-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:25.49731+00:00
-- url     : https://prove2.me/submissions/708302cf-d5fd-4afc-a105-0bf0ee401bf5

-- Generated proof for MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous.
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









/-! ### Right-register variant of `triangleSub` -/

theorem solution
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ιA)
    (B D : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιB) (δ ε : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) δ)
    (hBD : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D)) ε) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by
  let AL : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) A
  let BR : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)
  let DR : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D)
  let matchB : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    ∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((AL q).outcome a * (DR q).outcome a)
  let overlap : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A q).total))
  let sdd : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q =>
    _root_.LIDT.MIPStarRE.LDT.qSDD ψ (BR q) (DR q)
  let gap : Question → _root_.LIDT.MIPStarRE.LDT.Error := fun q => matchB q - matchD q
  rcases hAB with ⟨hAB⟩
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [gap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hgap_avg_abs :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => _root_.LIDT.MIPStarRE.LDT.qSDD_nonneg ψ (BR q) (DR q))
  have hdefect_pointwise :
      ∀ q, _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (DR q) ≤ _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (BR q) + |gap q| := by
    intro q
    have hdefB :
        _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (BR q) = max 0 (overlap q - matchB q) := by
      unfold _root_.LIDT.MIPStarRE.LDT.qConsDefect _root_.LIDT.MIPStarRE.LDT.qMatchMass
      dsimp [overlap, matchB, AL, BR]
      rw [show
        ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) A q).total) *
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) q).total) =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A q).total) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((B q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas,
        _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor]
    have hdefD :
        _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (DR q) = max 0 (overlap q - matchD q) := by
      unfold _root_.LIDT.MIPStarRE.LDT.qConsDefect _root_.LIDT.MIPStarRE.LDT.qMatchMass
      dsimp [overlap, matchD, AL, DR]
      rw [show
        ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) A q).total) *
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D) q).total) =
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A q).total) *
            _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((D q).total) by rfl]
      rw [(D q).total_eq_one]
      simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas,
        _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor]
    calc
      _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (DR q)
        = max 0 ((overlap q - matchB q) + gap q) := by
            rw [hdefD]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchB q) + |gap q| := _root_.LIDT.MIPStarRE.LDT.Preliminaries.max_zero_add_le _ _
      _ = _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (BR q) + |gap q| := by
            rw [hdefB]
  constructor
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed]
  unfold _root_.LIDT.MIPStarRE.LDT.consError _root_.LIDT.MIPStarRE.LDT.sddError at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (DR q))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (BR q) + |gap q|) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ (AL q) (BR q)) +
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => |gap q|) := by
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
    _ ≤ δ + Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 sdd) := by
          exact add_le_add hAB hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hBD) δ
