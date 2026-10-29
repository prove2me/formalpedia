-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.avg_postprocess_sandwichTensor_eq_diag_add_collision
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:00:32.114458+00:00
-- url     : https://prove2.me/submissions/0249d192-920d-4e81-a326-f0e2d069d138

-- Generated proof for MIPStarRE.LDT.Commutativity.avg_postprocess_sandwichTensor_eq_diag_add_collision.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean. -/
/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













/-- Expand the expectation of a tensor sandwich whose inner/right family is an
indicator-restricted finite sum. -/
private lemma ev_sandwichTensor_indicator_expand
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (A : α → MIPStarRE.Quantum.Op ι)
    (p : α → Prop) [DecidablePred p] :
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0)) =
      ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
  classical
  let S : MIPStarRE.Quantum.Op ι := ∑ a : α, if p a then A a else 0
  have hleft :
      leftTensor (ι₂ := ι) (B * S * B) =
        ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
    calc
      leftTensor (ι₂ := ι) (B * S * B)
        = leftTensor (ι₂ := ι) (∑ a : α, if p a then B * A a * B else 0) := by
            congr 1
            simp [S, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
      _ = ∑ a : α, leftTensor (ι₂ := ι) (if p a then B * A a * B else 0) := by
            exact (leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => if p a then B * A a * B else 0)).symm
      _ = ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, leftTensor]
  have hright :
      rightTensor (ι₁ := ι) S =
        ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
    calc
      rightTensor (ι₁ := ι) S
        = ∑ a : α, rightTensor (ι₁ := ι) (if p a then A a else 0) := by
            exact (rightTensor_finset_sum (ι₁ := ι) Finset.univ
              (fun a : α => if p a then A a else 0)).symm
      _ = ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, rightTensor]
  calc
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0))
      = ev ψ ((∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0) *
          (∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0)) := by
          have hleft' :
              leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) =
                ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            simpa [S] using hleft
          have hright' :
              rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0) =
                ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            simpa [S] using hright
          rw [hleft', hright']
    _ = ev ψ (∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [Finset.mul_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          ev ψ ((if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [ev_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A a₁ * B) *
              rightTensor (ι₁ := ι) (A a₂)) := by
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂ <;> simp [h₁, h₂, ev_zero]
    _ = ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
          exact (Fintype.sum_prod_type' (f := fun a₁ : α => fun a₂ : α =>
            (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
              ev ψ
                (leftTensor (ι₂ := ι) (B * A a₁ * B) *
                  rightTensor (ι₁ := ι) (A a₂)))).symm

/-- Sum over the postprocessed outcome label of two matching indicators. -/
private lemma postprocess_collision_coeff_sum
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : α → κ) (a₁ a₂ : α) :
    (∑ k : κ,
        if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) =
      (if f a₁ = f a₂ then (1 : Error) else 0) := by
  classical
  by_cases h : f a₁ = f a₂
  · calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0)
        = ∑ k : κ, if f a₁ = k then (1 : Error) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            by_cases hk : f a₁ = k
            · have hk₂ : f a₂ = k := h.symm.trans hk
              simp [hk, hk₂]
            · simp [hk]
      _ = (1 : Error) := by
            rw [Fintype.sum_ite_eq]
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]
  · have hzero :
        ∀ k : κ,
          (if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
      intro k
      by_cases h₁ : f a₁ = k
      · by_cases h₂ : f a₂ = k
        · exact (h (h₁.trans h₂.symm)).elim
        · simp [h₁, h₂]
      · simp [h₁]
    calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
            exact Finset.sum_eq_zero (fun k _ => hzero k)
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]

/-- Expand a postprocessed tensor sandwich into the pair-collision expression for
one fixed sample. -/
private lemma postprocess_sandwichTensor_expand
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (f : α → κ) :
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k))) =
    (∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2))) := by
  classical
  calc
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)))
      = ∑ b : β, ∑ k : κ,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)) := by
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ k : κ, ∑ aa : α × α,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro k _
          have hpost :
              (postprocess A f).outcome k =
                ∑ a : α, if f a = k then A.outcome a else 0 := by
            unfold postprocess
            dsimp
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : f a = k <;> simp [ha]
          rw [hpost]
          simpa [mul_assoc] using ev_sandwichTensor_indicator_expand (ψ := ψ) (B := B.outcome b)
            (A := A.outcome) (p := fun a : α => f a = k)
    _ = ∑ b : β, ∑ aa : α × α, ∑ k : κ,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ aa : α × α,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro aa _
          calc
            (∑ k : κ,
                (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                  ev ψ
                    (leftTensor (ι₂ := ι)
                        (B.outcome b * A.outcome aa.1 * B.outcome b) *
                      rightTensor (ι₁ := ι) (A.outcome aa.2)))
              = (∑ k : κ,
                  if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [Finset.sum_mul]
            _ = (if f aa.1 = f aa.2 then (1 : Error) else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [postprocess_collision_coeff_sum f aa.1 aa.2]
    _ = ∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rw [Finset.sum_comm]

/-- Summing a pair-indexed expression against the diagonal indicator leaves the
ordinary diagonal sum. -/
private lemma diagonal_pair_sum
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (T : α × α → β → Error) :
    (∑ aa : α × α, ∑ b : β,
        (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) =
      ∑ a : α, ∑ b : β, T (a, a) b := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a₁ _
  calc
    (∑ a₂ : α, ∑ b : β,
        (if a₁ = a₂ then (1 : Error) else 0) * T (a₁, a₂) b)
      = ∑ a₂ : α, if a₁ = a₂ then (∑ b : β, T (a₁, a₂) b) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h : a₁ = a₂ <;> simp [h]
    _ = ∑ b : β, T (a₁, a₁) b := by
          rw [Fintype.sum_ite_eq]











end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (A : _root_.LIDT.MIPStarRE.LDT.SubMeas α ι) (B : _root_.LIDT.MIPStarRE.LDT.SubMeas β ι) (eval : σ → α → κ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (B.outcome b * (_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)) *
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
  classical
  let 𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution σ := _root_.LIDT.MIPStarRE.LDT.uniformDistribution σ
  let T : α × α → β → _root_.LIDT.MIPStarRE.LDT.Error := fun aa b =>
    _root_.LIDT.MIPStarRE.LDT.ev ψ
      (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome aa.2))
  let c : α × α → _root_.LIDT.MIPStarRE.LDT.Error := fun aa =>
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun s => if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
  have hc_diag (a : α) : c (a, a) = 1 := by
    simp [c, 𝒟, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                (B.outcome b * (_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) ((_root_.LIDT.MIPStarRE.LDT.postprocess A (eval s)).outcome k)))
      = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun s => ∑ aa : α × α, ∑ b : β,
          (if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) * T aa b) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro s
          simpa [T] using
            postprocess_sandwichTensor_expand (ψ := ψ) (A := A) (B := B)
              (f := eval s)
    _ = ∑ aa : α × α, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
            (fun s =>
              (if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) * T aa b) := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
    _ = ∑ aa : α × α, ∑ b : β, c aa * T aa b := by
          refine Finset.sum_congr rfl ?_
          intro aa _
          refine Finset.sum_congr rfl ?_
          intro b _
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const 𝒟
            (fun s => if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) (T aa b)
    _ = (∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) * T aa b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro b _
          by_cases h : aa.1 = aa.2
          · have hc : c aa = 1 := by
              rcases aa with ⟨a₁, a₂⟩
              dsimp at h ⊢
              subst a₂
              exact hc_diag a₁
            simp [h, hc]
          · simp [h]
    _ = (∑ a : α, ∑ b : β, T (a, a) b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [diagonal_pair_sum]
    _ = (∑ a : α, ∑ b : β,
          _root_.LIDT.MIPStarRE.LDT.ev ψ
            (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)) *
            _root_.LIDT.MIPStarRE.LDT.ev ψ
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rfl
