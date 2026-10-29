-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_once_commuted_contraction_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:03:35.813387+00:00
-- url     : https://prove2.me/submissions/9ef95395-c45f-441e-9d4b-384da58d6a91

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_once_commuted_contraction_left.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_projSubMeas_sandwich_sum_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFourthTermX_sum

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean. -/
/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/











/-- The total operator of a projective submeasurement is idempotent. -/
lemma projSubMeas_total_sq
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome ι) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total := by
  simpa using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooContraction/Split.lean. -/
/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and first mixed-term transfer.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Shared switcheroo contraction helper definitions -/



/-- The complete-part total operator is Hermitian. -/
lemma switcherooCompletePartTotal_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    ((completePartSubMeas params family q.1).total)ᴴ =
      (completePartSubMeas params family q.1).total :=
  (Matrix.nonneg_iff_posSemidef.mp
    (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq

/-- The complete-part total operator is idempotent. -/
lemma switcherooCompletePartTotal_sq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total *
        (completePartSubMeas params family q.1).total =
      (completePartSubMeas params family q.1).total := by
  simpa [completePartSubMeas, postprocess_total] using
    projSubMeas_total_sq (family.meas q.1)

/-- The complete-part total operator is bounded by the identity. -/
lemma switcherooCompletePartTotal_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total ≤ 1 :=
  (completePartSubMeas params family q.1).total_le_one

/-- Every outcome of the external projective family is Hermitian. -/
lemma switcherooMeasuredOutcome_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (o : Outcome) :
    ((M q.2).outcome o)ᴴ = (M q.2).outcome o :=
  (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq

/-- Every slice outcome of the completed family is Hermitian. -/
lemma switcherooSliceOutcome_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    ((family.meas q.1).outcome g)ᴴ = (family.meas q.1).outcome g :=
  (Matrix.nonneg_iff_posSemidef.mp ((family.meas q.1).outcome_pos g)).isHermitian.eq

/-- The shared `X_g` sandwich family is Hermitian pointwise. -/
lemma switcherooAggregateFourthTermX_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    (switcherooAggregateFourthTermX params family M q g)ᴴ =
      switcherooAggregateFourthTermX params family M q g := by
  unfold switcherooAggregateFourthTermX
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro o _
  simp [Matrix.conjTranspose_mul, switcherooMeasuredOutcome_hermitian params M q o,
    switcherooSliceOutcome_hermitian params family q g, mul_assoc]

/-- The shared `X_g` sandwich family is positive semidefinite pointwise. -/
lemma switcherooAggregateFourthTermX_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    0 ≤ switcherooAggregateFourthTermX params family M q g := by
  unfold switcherooAggregateFourthTermX
  refine Finset.sum_nonneg ?_
  intro o _
  exact IsSelfAdjoint.conjugate_nonneg ((family.meas q.1).outcome_pos g)
    (switcherooMeasuredOutcome_hermitian params M q o)

/-- The shared `X_g` sandwich family is bounded by the identity pointwise. -/
lemma switcherooAggregateFourthTermX_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    switcherooAggregateFourthTermX params family M q g ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((family.meas q.1).outcome g)
    ((family.meas q.1).outcome_le_one g)

/-- The shared `X_g` sandwich family satisfies `X_g^2 ≤ X_g`. -/
lemma switcherooAggregateFourthTermX_sq_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    switcherooAggregateFourthTermX params family M q g *
        switcherooAggregateFourthTermX params family M q g ≤
      switcherooAggregateFourthTermX params family M q g :=
  MIPStarRE.Quantum.sq_le_self
    (switcherooAggregateFourthTermX_nonneg params family M q g)
    (switcherooAggregateFourthTermX_le_one params family M q g)



/-- The middle sandwich sum used in the contraction bounds is a contraction. -/
lemma switcherooAggregateFourthTerm_middle_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((completePartSubMeas params family q.1).total)
    (switcherooCompletePartTotal_le_one params family q)









end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and first mixed-term transfer.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Shared switcheroo contraction helper definitions -/

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (q : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :
    (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        (∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) *
          (∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ) ≤ 1 := by
  let G : _root_.LIDT.MIPStarRE.Quantum.Op ι := (_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total
  let Gq : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  let Mo : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op ι := (M q.2).outcome
  let X : _root_.LIDT.MIPStarRE.LDT.Polynomial params → _root_.LIDT.MIPStarRE.Quantum.Op ι :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX params family M q
  have hGherm : Gᴴ = G := by
    simpa [G] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := by
    simpa [G] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooCompletePartTotal_sq params family q
  have hMoherm : ∀ o : Outcome, (Mo o)ᴴ = Mo o := by
    intro o
    simpa [Mo] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooMeasuredOutcome_hermitian params M q o
  have hGqherm : ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (Gq g)ᴴ = Gq g := by
    intro g
    simpa [Gq] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooSliceOutcome_hermitian params family q g
  have hXherm : ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, (X g)ᴴ = X g := by
    intro g
    simpa [X] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX_hermitian params family M q g
  have hXnonneg : ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, 0 ≤ X g := by
    intro g
    simpa [X] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX_nonneg params family M q g
  have hXle : ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g ≤ 1 := by
    intro g
    simpa [X] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX_le_one params family M q g
  have hXsq_le : ∀ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g * X g ≤ X g := by
    intro g
    simpa [X] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX_sq_le params family M q g
  have hsum :
      (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
          (∑ o : Outcome, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o)) *
            (∑ o : Outcome, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))ᴴ) =
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * X g * G) := by
    refine Finset.sum_congr rfl ?_
    intro g _
    calc
      (∑ o : Outcome, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o)) *
          (∑ o : Outcome, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))ᴴ
        = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g) * (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g))ᴴ := by
            congr 2
            · rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
                (fun o : Outcome => G * Mo o * Gq g * Mo o)]
              congr 1
              simpa [X, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX, mul_assoc] using
                (Finset.mul_sum (s := Finset.univ) (a := G)
                  (f := fun o : Outcome => Mo o * Gq g * Mo o)).symm
            · rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
                (fun o : Outcome => G * Mo o * Gq g * Mo o)]
              congr 1
              simpa [X, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX, mul_assoc] using
                (Finset.mul_sum (s := Finset.univ) (a := G)
                  (f := fun o : Outcome => Mo o * Gq g * Mo o)).symm
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g) * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((G * X g)ᴴ) := by
            congr 2
            simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
              (_root_.LIDT.MIPStarRE.LDT.conjTranspose_opTensor (G * X g) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) ((G * X g) * (G * X g)ᴴ) := by
            rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
      _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * X g * G) := by
            simp [Matrix.conjTranspose_mul, hGherm, hXherm g, mul_assoc]
  have hsandwichSum_le :
      (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * X g * G)) ≤
        ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * G) := by
    refine Finset.sum_le_sum ?_
    intro g _
    simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
      (_root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (ι₂ := ι) (B := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
        (by simpa [mul_assoc] using IsSelfAdjoint.conjugate_le_conjugate (hXsq_le g) hGherm)
        (show (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
  have hsumX : ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g = ∑ o : Outcome, Mo o * G * Mo o := by
    simpa [X, G, Mo] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTermX_sum params family M q
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    simpa [G, Mo] using _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsandwich_le : G * (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g) * G ≤ G := by
    calc
      G * (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g) * G ≤ G * 1 * G := by
        exact IsSelfAdjoint.conjugate_le_conjugate (by simpa [hsumX] using hmid_le) hGherm
      _ = G := by simp [hGsq]
  calc
    (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params,
        (∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) *
          (∑ o : Outcome,
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
              ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ)
      = ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * X g * G) := by
          simpa [G, Gq, Mo] using hsum
    _ ≤ ∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * X g * G) := hsandwichSum_le
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (G * (∑ g : _root_.LIDT.MIPStarRE.LDT.Polynomial params, X g) * G) := by
          rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι) Finset.univ
            (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => G * X g * G)]
          congr 1
          simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) G := by
          simpa [_root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.opTensor] using
            (_root_.LIDT.MIPStarRE.LDT.opTensor_mono_left (ι₂ := ι) (B := (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
              hsandwich_le (show (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
    _ ≤ 1 := by
          simpa [G] using _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one (ι₂ := ι)
            ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total_le_one)
