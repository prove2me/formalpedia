-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.simeqTriangleInequality_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:51.509343+00:00
-- url     : https://prove2.me/submissions/0fece7f0-d417-42d0-aa2b-865930091015

-- Generated proof for MIPStarRE.LDT.Preliminaries.simeqTriangleInequality_heterogeneous.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_simeqToApprox_heterogeneous
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_triangleSub_right_heterogeneous

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Triangle Inequalities for State-Dependent Distance: Simultaneous Equivalence

This module contains the simultaneous-equivalence triangle inequalities and the
final approximate-delta triangle estimate.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A C : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιA)
    (B D : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιB)
    (ε δ γ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) ε)
    (hCB : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C)
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) δ)
    (hCD : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C)
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D) γ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D)
      (ε + 2 * Real.sqrt (δ + γ)) := by
  have hCB_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (2 * δ) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous ψ 𝒟 C B δ hCB
  have hCD_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D))
      (2 * γ) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous ψ 𝒟 C D γ hCD
  have hBC_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C))
      (2 * δ) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddRel_symm ψ 𝒟 _ _ _ hCB_sdd
  have hBD_sdd_raw : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D))
      (2 * ((2 * δ) + (2 * γ))) := by
    exact
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_triangle ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas C))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D))
        (2 * δ) (2 * γ) hBC_sdd hCD_sdd
  have hBD_sdd : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D))
      (4 * (δ + γ)) := by
    exact
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D))
        (2 * ((2 * δ) + (2 * γ))) (4 * (δ + γ))
        (by
          ring_nf
          linarith)
        hBD_sdd_raw
  have hδ_nonneg : 0 ≤ δ := by
    rcases hCB with ⟨hδ⟩
    exact le_trans (_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg ψ 𝒟 _ _) hδ
  have hγ_nonneg : 0 ≤ γ := by
    rcases hCD with ⟨hγ⟩
    exact le_trans (_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg ψ 𝒟 _ _) hγ
  have hsqrt_four :
      Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    have hδγ_nonneg : 0 ≤ δ + γ := add_nonneg hδ_nonneg hγ_nonneg
    calc
      Real.sqrt (4 * (δ + γ))
        = Real.sqrt (4 : _root_.LIDT.MIPStarRE.LDT.Error) * Real.sqrt (δ + γ) := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : _root_.LIDT.MIPStarRE.LDT.Error) by positivity)]
      _ = 2 * Real.sqrt (δ + γ) := by norm_num
  have hfinal :
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D)
        (ε + Real.sqrt (4 * (δ + γ))) := by
    exact
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous ψ 𝒟 hψ h𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) B D ε (4 * (δ + γ))
        hAB hBD_sdd
  exact
    (by
      simpa [hsqrt_four] using hfinal)
