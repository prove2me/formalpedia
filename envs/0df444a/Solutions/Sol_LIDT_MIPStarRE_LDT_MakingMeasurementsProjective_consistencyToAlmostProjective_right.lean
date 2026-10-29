-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective_right
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:14:57.545438+00:00
-- url     : https://prove2.me/submissions/f22d2722-13be-4a8b-b029-72166f111731

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective_right.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean. -/
/-!
# Section 5 — Rounding To Projectors Core

Internal lemmas for the orthogonalization and rounding-to-projectors chain.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/















/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/


/-- The consistency defect of `(A,B)` controls the strong self-consistency
defect of the right-placed version of `B`.  This is the right-register
counterpart of `qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect`;
it uses the same Cauchy--Schwarz calculation with the two diagonal terms
interchanged. -/
private lemma qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  classical
  let diagA : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome,
      ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let defect : Error := qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas
  have hdefect_nonneg : 0 ≤ defect :=
    qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA :=
    sum_ev_leftTensor_outcome_sq_nonneg (ιB := ιB) ψ A.toSubMeas
  have hdiagB_nonneg : 0 ≤ diagB :=
    sum_ev_rightTensor_outcome_sq_nonneg (ιA := ιA) ψ B.toSubMeas
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (rightTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hleftPlaced_outcome :
      ∀ a : Outcome,
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
    intro a
    rfl
  have hleftPlaced_total :
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total =
        leftTensor (ι₂ := ιB) A.total :=
    rfl
  have hrightPlaced_outcome :
      ∀ a : Outcome,
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
    intro a
    rfl
  have hrightPlaced_total :
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total =
        rightTensor (ι₁ := ιA) B.total :=
    rfl
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, hleftPlaced_outcome, hleftPlaced_total, leftTensor_mul_leftTensor,
          A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, hrightPlaced_outcome, hrightPlaced_total,
          rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass :=
    sum_ev_opTensor_outcome_le_totalMass (ψ := ψ) A B
  have habs : |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB :=
    abs_sum_ev_opTensor_le_sqrt_mul_sqrt (ψ := ψ) A.toSubMeas B.toSubMeas
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      have hoverlap_nonneg : 0 ≤ overlap :=
        Finset.sum_nonneg fun a _ =>
          ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
      nlinarith [hoverlap_nonneg, hoverlap_upper,
        Real.sqrt_nonneg diagA, Real.sqrt_nonneg diagB]
    calc
      overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := hsq
      _ = diagA * diagB := by
            ring_nf
            rw [Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hdiagB_nonneg]
  have hdefect_eq : defect = totalMass - overlap := by
    have hoverlap_le_totalOverlap :
        overlap ≤ ev ψ (opTensor A.total B.total) := by
      simpa [totalMass, A.total_eq_one, B.total_eq_one, opTensor] using hoverlap_le
    dsimp [defect]
    unfold qBipartiteConsDefect
    rw [show qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas = overlap by rfl]
    rw [show (let totalOverlap := ev ψ (opTensor A.total B.total);
          max 0 (totalOverlap - overlap)) =
        max 0 (ev ψ (opTensor A.total B.total) - overlap) by rfl]
    rw [max_eq_right (sub_nonneg.mpr hoverlap_le_totalOverlap)]
    simp [totalMass, A.total_eq_one, B.total_eq_one, opTensor]
  have hoverlap_sq' : overlap ^ 2 ≤ diagB * diagA := by
    rw [mul_comm]
    exact hoverlap_sq
  have hdiagB_lower : totalMass - 2 * defect ≤ diagB :=
    totalMass_sub_two_defect_le_diagA
      hdiagB_nonneg hdefect_nonneg hdefect_eq hoverlap_sq' hdiagA_le
  have hinner : totalMass - diagB ≤ 2 * defect := by linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by linarith
  have hmax : max 0 (totalMass - diagB) ≤ 2 * defect :=
    max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) -
        diagB) ≤ 2 * defect := by
    simpa [hright_one] using hmax
  simpa [qSSCDefect, diagB, hrightPlaced_outcome, hrightPlaced_total,
    rightTensor_mul_rightTensor, B.total_eq_one] using hmax'















end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT

open LIDT
/-!
# Section 5 — Rounding To Projectors Core

Internal lemmas for the orthogonalization and rounding-to-projectors chain.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/















/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/

theorem solution {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιB) (ζ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) ζ →
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement ψ
        (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B)
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  classical
  let B_lifted : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (ιA × ιB) :=
    _root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B
  have hCons' :
      _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily] using
      hCons.offDiagonalBound
  have hζ_nonneg : 0 ≤ ζ := by
    exact le_trans (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas) hCons'
  have hsscBound :
      _root_.LIDT.MIPStarRE.LDT.qSSCDefect ψ B_lifted.toSubMeas ≤ _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError ζ := by
    calc
      _root_.LIDT.MIPStarRE.LDT.qSSCDefect ψ B_lifted.toSubMeas
        ≤ 2 * _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
            simpa [B_lifted, _root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas] using
              qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect
                (ψ := ψ) A B
      _ ≤ 2 * ζ := by
            exact mul_le_mul_of_nonneg_left hCons' (by norm_num)
      _ = _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError ζ := by
            simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    rw [_root_.LIDT.MIPStarRE.LDT.Preliminaries.constFamily_ssc_unit]
    exact hsscBound
  · constructor
    calc
      _root_.LIDT.MIPStarRE.LDT.sddError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B_lifted.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B_lifted.toSubMeas)
        = 0 := _root_.LIDT.MIPStarRE.LDT.sddError_self ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) _
      _ ≤ 2 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError ζ := by
            dsimp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError]
            nlinarith [hζ_nonneg]
  · exact sourceAlmostProjective_of_ssc ψ B_lifted _ hsscBound
