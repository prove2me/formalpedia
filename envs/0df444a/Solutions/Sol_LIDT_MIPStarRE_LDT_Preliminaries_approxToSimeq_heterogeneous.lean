-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:11:33.330465+00:00
-- url     : https://prove2.me/submissions/7ed5885e-64d0-4625-992a-2693ae8c1773

-- Generated proof for MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
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

/- Source helpers from MIPStarRE/LDT/Preliminaries/ComparisonProjective.lean. -/
/-!
# Preliminary comparison theorems: projective converse

Projective-case converse of `prop:simeq-to-approx`. This lemma lives in a
sibling module to `ComparisonCore` because its proof uses
`projSubMeas_diagMass_eq_mass`, which is introduced in
`SwitchSandwichPrep.Core`, downstream of `ComparisonCore`.

The imports above are chosen to make the direct dependencies explicit rather
than relying on transitive re-exports through `SwitchSandwichPrep.Core`:
`ComparisonCore` is the sibling comparison module, `ConsistencyBridges`
supplies the `BipartiteSDDRel`/`ConsRel` bridging machinery, and
`SwitchSandwichPrep.Core` provides `projSubMeas_diagMass_eq_mass`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT





-- The heterogeneous proof expands the projective identity on the tensor-product
-- space; the final algebra is the same as the same-space theorem above, but the
-- generated matrix expressions are larger.
private lemma two_questionConsistency_eq_questionSDD_of_projective_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A : ProjMeas Outcome ιA) (B : ProjMeas Outcome ιB) :
    2 * qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) =
      qSDD ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) := by
  let ALeft : ProjSubMeas Outcome (ιA × ιB) :=
    { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
      proj := fun a => by simp [leftPlacedSubMeas, leftTensor_mul_leftTensor, A.proj a] }
  let BRight : ProjSubMeas Outcome (ιA × ιB) :=
    { toSubMeas := rightPlacedSubMeas (ιA := ιA) B.toSubMeas
      proj := fun a => by simp [rightPlacedSubMeas, rightTensor_mul_rightTensor, B.proj a] }
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)
  have hdiagA :
      ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a) = totalMass := by
    calc
      ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)
        = ev ψ ALeft.total := projSubMeas_diagMass_eq_mass ψ ALeft
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by rfl
      _ = ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
            rw [A.total_eq_one]
      _ = totalMass := by
            rw [leftTensor_one (ι₁ := ιA) (ι₂ := ιB)]
  have hdiagB :
      ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a) = totalMass := by
    calc
      ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)
        = ev ψ BRight.total := projSubMeas_diagMass_eq_mass ψ BRight
      _ = ev ψ (rightTensor (ι₁ := ιA) B.total) := by rfl
      _ = ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [B.total_eq_one]
      _ = totalMass := by
            rw [rightTensor_one (ι₁ := ιA) (ι₂ := ιB)]
  have h_expand :
      ∀ a : Outcome,
        ev ψ (((ALeft.outcome a - BRight.outcome a)ᴴ) *
              (ALeft.outcome a - BRight.outcome a)) =
          ev ψ (ALeft.outcome a * ALeft.outcome a) +
            ev ψ (BRight.outcome a * BRight.outcome a) -
            2 * ev ψ (ALeft.outcome a * BRight.outcome a) := by
    intro a
    have hcomm :
        ev ψ (BRight.outcome a * ALeft.outcome a) =
          ev ψ (ALeft.outcome a * BRight.outcome a) :=
      ev_mul_comm_of_psd ψ _ _ (BRight.outcome_pos a) (ALeft.outcome_pos a)
    calc
      ev ψ (((ALeft.outcome a - BRight.outcome a)ᴴ) *
            (ALeft.outcome a - BRight.outcome a))
        = ev ψ ((ALeft.outcome a * ALeft.outcome a - ALeft.outcome a * BRight.outcome a) -
            (BRight.outcome a * ALeft.outcome a - BRight.outcome a * BRight.outcome a)) := by
              congr 1
              simp [sub_mul, mul_sub, ProjSubMeas.outcome_hermitian]
              abel
      _ = ev ψ (ALeft.outcome a * ALeft.outcome a) -
            ev ψ (ALeft.outcome a * BRight.outcome a) -
            (ev ψ (BRight.outcome a * ALeft.outcome a) -
              ev ψ (BRight.outcome a * BRight.outcome a)) := by
              rw [ev_sub, ev_sub, ev_sub]
      _ = ev ψ (ALeft.outcome a * ALeft.outcome a) +
            ev ψ (BRight.outcome a * BRight.outcome a) -
            2 * ev ψ (ALeft.outcome a * BRight.outcome a) := by
              rw [hcomm]
              ring
  have hqSDD :
      qSDD ψ
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) =
        2 * (totalMass - overlap) := by
    unfold qSDD qSDDCore overlap
    calc
      ∑ a : Outcome,
          ev ψ
            ((((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
                (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a)ᴴ) *
              ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
                (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a))
        = ∑ a : Outcome,
            (ev ψ (ALeft.outcome a * ALeft.outcome a) +
              ev ψ (BRight.outcome a * BRight.outcome a) -
              2 * ev ψ (ALeft.outcome a * BRight.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa [ALeft, BRight] using h_expand a
      _ = (∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)) +
            (∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)) -
            2 * ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * (totalMass - overlap) := by
              rw [hdiagA, hdiagB]
              simp [overlap]
              ring
  have hgap_nonneg : 0 ≤ totalMass - overlap := by
    have hnonneg :=
      qSDD_nonneg ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
    rw [hqSDD] at hnonneg
    linarith
  have hqCons :
      qConsDefect ψ
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) =
        totalMass - overlap := by
    unfold qConsDefect qMatchMass
    have htotal :
        ev ψ
            ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total *
              (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total)
          = totalMass := by
      calc
        ev ψ
            ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total *
              (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total)
          = ev ψ (leftTensor (ι₂ := ιB) A.total * rightTensor (ι₁ := ιA) B.total) := by
              rfl
        _ = ev ψ
              (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA) *
                rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
              rw [A.total_eq_one, B.total_eq_one]
        _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
              rw [leftTensor_one (ι₁ := ιA) (ι₂ := ιB),
                rightTensor_one (ι₁ := ιA) (ι₂ := ιB)]
              simp
        _ = totalMass := rfl
    rw [htotal, max_eq_right hgap_nonneg]
  calc
    2 * qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
      = 2 * (totalMass - overlap) := by rw [hqCons]
    _ = qSDD ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) := by rw [hqSDD]



end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Preliminary comparison theorems: projective converse

Projective-case converse of `prop:simeq-to-approx`. This lemma lives in a
sibling module to `ComparisonCore` because its proof uses
`projSubMeas_diagMass_eq_mass`, which is introduced in
`SwitchSandwichPrep.Core`, downstream of `ComparisonCore`.

The imports above are chosen to make the direct dependencies explicit rather
than relying on transitive re-exports through `SwitchSandwichPrep.Core`:
`ComparisonCore` is the sibling comparison module, `ConsistencyBridges`
supplies the `BipartiteSDDRel`/`ConsRel` bridging machinery, and
`SwitchSandwichPrep.Core` provides `projSubMeas_diagMass_eq_mass`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT





-- The heterogeneous proof expands the projective identity on the tensor-product
-- space; the final algebra is the same as the same-space theorem above, but the
-- generated matrix expressions are larger.

theorem solution {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Question Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Question Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B))
        (2 * δ) →
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A)
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B) δ := by
  intro ⟨happrox⟩
  constructor
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed]
  unfold _root_.LIDT.MIPStarRE.LDT.consError _root_.LIDT.MIPStarRE.LDT.sddError at *
  have h_two_avg :
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A)) q)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B)) q)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qSDD ψ
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A)) q)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B)) q)) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_
    intro q
    simpa [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas,
      _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas] using
      two_questionConsistency_eq_questionSDD_of_projective_heterogeneous ψ (A q) (B q)
  change _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ
          ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A)) q)
          ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B)) q)) ≤ δ
  linarith
