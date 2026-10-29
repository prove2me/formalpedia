-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.consSubMeas
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:11:33.290484+00:00
-- url     : https://prove2.me/submissions/259b013f-cf8d-4fb1-ad64-9d6f7051ccc0

-- Generated proof for MIPStarRE.LDT.Preliminaries.consSubMeas.
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

/- Source helpers from MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean. -/
/-!
# Preliminary comparison theorems: consistency-to-distance estimates

Estimates converting consistency of a submeasurement and a measurement into
state-dependent distance controls for the diagonal and total sandwich families
of `prop:cons-sub-meas`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Consistency controls for `prop:cons-sub-meas` -/

private lemma consSubMeas_controlHelper
    {Outcome : Type*} {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (P Q M N : SubMeas Outcome κ)
    (X : Outcome → MIPStarRE.Quantum.Op κ)
    (hSq :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) =
          ev ψ (X a * X a))
    (hX_nonneg : ∀ a : Outcome, 0 ≤ X a)
    (hX_le_one : ∀ a : Outcome, X a ≤ 1)
    (hSum :
      ∑ a : Outcome, ev ψ (X a) =
        ev ψ (P.total * Q.total) - qMatchMass ψ P Q) :
    qSDD ψ M N ≤ qConsDefect ψ P Q := by
  have hsummand :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) ≤
          ev ψ (X a) := by
    intro a
    calc
      ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
        = ev ψ (X a * X a) := hSq a
      _ ≤ ev ψ (X a) := by
          exact ev_mono ψ _ _ (MIPStarRE.Quantum.sq_le_self (hX_nonneg a) (hX_le_one a))
  have hnonneg :
      0 ≤ ev ψ (P.total * Q.total) - qMatchMass ψ P Q := by
    calc
      0 ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_nonneg fun a _ =>
            ev_nonneg_of_psd ψ _ (hX_nonneg a)
      _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum
  unfold qSDD qSDDCore qConsDefect
  rw [max_eq_right hnonneg]
  calc
    ∑ a : Outcome,
        ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
      ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_le_sum fun a _ => hsummand a
    _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum

private lemma consSubMeas_diagonalControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
      (diagonalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((IdxSubMeas.liftLeft A) q) ((diagonalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((IdxSubMeas.liftLeft A) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [IdxSubMeas.liftLeft, diagonalSandwichFamily,
              LDT.leftTensor_mul_rightTensor_eq_opTensor, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_le_leftTensor
              ((A q).outcome_pos a)
              (Measurement.outcome_le_one (B q) a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_left :
                X a ≤ ((IdxSubMeas.liftLeft A) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            exact le_trans hX_le_left <|
              leftTensor_le_one (ι₂ := ι) ((A q).outcome_le_one a)
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((IdxSubMeas.liftLeft A) q))
            (((diagonalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            simp [X, hXh]
          · have hleft :
                ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
              simp [leftTensor_finset_sum, (A q).sum_eq_total]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                    ∑ a : Outcome,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                          simp [X, IdxSubMeas.liftLeft,
                            diagonalSandwichFamily, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                          unfold qMatchMass
                          simp [hleft, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                            IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        have htotalOverlap :
                            ev ψ
                                ((((IdxSubMeas.liftLeft A) q).total) *
                                  (((IdxSubMeas.liftRight
                                      (IdxMeas.toIdxSubMeas B)) q).total)) =
                              ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                          rw [show (((IdxSubMeas.liftLeft A) q).total) *
                              (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total) =
                                leftTensor (ι₂ := ι) ((A q).total) *
                                  rightTensor (ι₁ := ι) ((B q).total) by rfl]
                          rw [(B q).total_eq_one]
                          simp [leftTensor, rightTensor]
                        rw [htotalOverlap]
    _ ≤ γ := by
      simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxSubMeas.placeLeft,
        IdxSubMeas.placeRight, leftPlacedSubMeas, rightPlacedSubMeas,
        IdxMeas.toIdxSubMeas] using hcons

private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((diagonalSandwichFamily A B) q) ((totalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((totalSandwichFamily A B) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [totalSandwichFamily, LDT.leftTensor_mul_rightTensor_eq_opTensor,
              diagonalSandwichFamily, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_mono_left
              ((A q).outcome_le_total a)
              ((B q).outcome_pos a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_total :
                X a ≤ ((totalSandwichFamily A B) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            have htotal_le :
                ((totalSandwichFamily A B) q).outcome a ≤ 1 := by
              dsimp [totalSandwichFamily]
              have hop :
                  opTensor ((A q).total) ((B q).outcome a) ≤
                    leftTensor (ι₂ := ι) ((A q).total) := by
                exact MIPStarRE.LDT.opTensor_le_leftTensor
                  ((A q).total_nonneg)
                  (Measurement.outcome_le_one (B q) a)
              simpa [MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor] using
                le_trans hop (leftTensor_le_one (ι₂ := ι) (A q).total_le_one)
            exact le_trans hX_le_total htotal_le
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((diagonalSandwichFamily A B) q))
            (((totalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            have hneg :
                ((diagonalSandwichFamily A B) q).outcome a -
                    ((totalSandwichFamily A B) q).outcome a =
                  -(X a) := by
              simp [X]
            simp [hneg, hXh]
          · have htotal :
                ∑ a : Outcome,
                    ev ψ
                      (((totalSandwichFamily A B) q).outcome a) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => ((totalSandwichFamily A B) q).outcome a)]
              calc
                ev ψ (∑ a : Outcome, ((totalSandwichFamily A B) q).outcome a)
                  =
                    ev ψ
                      (∑ a : Outcome,
                        leftTensor (ι₂ := ι) ((A q).total) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            simp [totalSandwichFamily]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        ∑ a : Outcome, rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            rw [← Finset.mul_sum]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) (∑ a : Outcome, (B q).outcome a)) := by
                            rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ
                              (fun a : Outcome => (B q).outcome a)]
                _ =
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) 1) := by
                            rw [(B q).sum_eq]
                _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                            simp [leftTensor, rightTensor]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (((totalSandwichFamily A B) q).outcome a) -
                    ∑ a : Outcome, ev ψ (((diagonalSandwichFamily A B) q).outcome a) := by
                        simp [X, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        unfold qMatchMass
                        simp [htotal, diagonalSandwichFamily, IdxSubMeas.liftLeft,
                          IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        rw [show ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total =
                            rightTensor (ι₁ := ι) ((B q).total) by rfl]
                        rw [(B q).total_eq_one]
                        simp [IdxSubMeas.liftLeft, rightTensor, leftTensor]
    _ ≤ γ := by
      simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxSubMeas.placeLeft,
        IdxSubMeas.placeRight, leftPlacedSubMeas, rightPlacedSubMeas,
        IdxMeas.toIdxSubMeas] using hcons










end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# Preliminary comparison theorems: consistency-to-distance estimates

Estimates converting consistency of a submeasurement and a measurement into
state-dependent distance controls for the diagonal and total sandwich families
of `prop:cons-sub-meas`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Consistency controls for `prop:cons-sub-meas` -/

theorem solution {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ι)
    (B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ι) (γ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) γ →
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.ConsSubMeasStmt ψ 𝒟 A B γ := by
  intro hcons
  have hdc := consSubMeas_diagonalControl ψ 𝒟 A B γ hcons
  have hsc := consSubMeas_sandwichControl ψ 𝒟 A B γ hcons
  have hcombined :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ 𝒟 (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft A)
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily A B) (2 * (γ + γ)) (4 * γ) (by linarith)
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_triangle ψ 𝒟 (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft A)
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.diagonalSandwichFamily A B) (_root_.LIDT.MIPStarRE.LDT.Preliminaries.totalSandwichFamily A B) γ γ hdc hsc)
  exact {
    diagonalControl := hdc
    sandwichControl := hsc
    combinedControl := hcombined
  }
